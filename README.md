# cl-ton

A TON blockchain client for Common Lisp (SBCL). It reads the chain with its own **verifying lite client**—every answer is proved against the config’s trust anchor, over a native Lisp proxy-liteserver—and runs get-methods and dry runs in `libemulator`. Around that: a Cell/BOC codec, wallet v5r1 signing, jetton support, and a generic DEX protocol. In production, it is the networking and contract layer of an automated trading system.

The only required shared library is `libemulator`. The JSON tonlib (`tonlibjson`) is kept as a **test oracle**; see [The JSON tonlib oracle (tests only)](#the-json-tonlib-oracle-tests-only).

### Warning

This project is under active development; please refer to the [`package.lisp`](./src/package.lisp) file to examine the interface.

## Layout

```text
cl-ton/
  src/
    package.lisp          the cl-ton package and everything it exports
    errors.lisp           the TON-ERROR condition hierarchy
    ton-boc.lisp          cell/builder/BOC codec, PMAP (see "Cells and BOC")
    slice.lisp            reading a cell back out: LOAD-UINT, LOAD-REF, ...
    base64.lisp, types.lisp   base64; address, coins, message-spec, dict encoding
    tl.lisp               TL codec + the lite_api / ton_api schema subset (constructor ids = CRC32)
    vm-stack.lisp         TVM stack <-> Lisp values (and tonlib's JSON stack format)
    emulator.lisp         libemulator FFI: local get-method runs and transaction emulation
    ed25519-batch.lisp    many Ed25519 signatures at once, on ironclad's curve operations
    proof-verify.lisp     a liteserver answer against a trusted block hash (Merkle proofs, accounts, shards)
    sync.lisp             trusted block -> newer block: validator-set signatures over block links
    adnl-ext*.lisp        ADNL-ext crypto/framing, outbound client, inbound listener
    proxy-liteserver.lisp the native Lisp proxy-liteserver (see "Networking")
    lite-client.lisp      the verifying client: sync, account state, transactions, getters, libraries
    lite-backend.lisp     the lite client behind the TONLIB-* surface
    tonlib.lisp           the chain-client surface (TONLIB-ACCOUNT-STATE, TONLIB-RUN-GET-METHOD, ...),
                          keystores, retries, getters; the seam to the test-only JSON tonlib
    wallet.lisp, jetton.lisp, dex.lisp   wallet v5r1; TEP-74 jettons; the generic DEX protocol (defgenerics only)
    indexer.lisp          shard-prefix matching, confirmed-transaction scanning
    chain.lisp            the CHAIN protocol and its implementation
  lib/                    libemulator-linux-x86_64.so
  tests/                  the cl-ton/test system (see "Testing")
    lib/                  TEST-ONLY native code: tonlibjson-linux-x86_64.so, compat/libgcc_s.so.1
    tonlib-oracle.lisp    the JSON tonlib (FFI + the TONLIB-JSON-OP methods)
    fakechain.lisp        the emulator-backed liteserver (the simulated network)
    fixtures/             captured real data (real/: mainnet block links, dex/: captured contracts)
    fift-linux-x86_64, proxy-liteserver-linux-x86_64   the released executables (A/B reference)
  cl-ton.asd
```

There are two ASDF systems: `cl-ton` (the library) and `cl-ton/test`. `files.lisp` and `fakechain.lisp` live under `tests/`, but are components of the test system, which also loads the JSON tonlib oracle first.

## The lite client

`open-lite-client` (normally reached through the TONLIB-* surface) trusts exactly one thing: the `init_block` of the global config. From it:

- **Key-block chain.** It walks block proofs forward to the newest key block, checking each link’s validator signatures against the validator set the previous key block committed to (ordinary and Simplex signature sets, weighted, two thirds required). The newest proved key block is kept in a state file in the keystore (checksum, owner, and mode checked, bound to the anchor), so only the first start walks the whole chain. That can take minutes on a weak link; later starts take seconds.
- **Heads and pinned reads.** `lite-sync` proves the newest masterchain head from the stored key block. Reads can be pinned to a block with `*get-method-block*`; the pool reads of a bot run in `PMAP` worker threads, so any special that must reach workers is listed in `*pmap-conveyed*`.
- **Proved reads.** Account states, shards, block transactions, and account transactions come with Merkle proofs checked against the proved block. The public libraries a contract refers to (STON.fi v2 keeps pool code in libraries) are fetched with `getLibrariesWithProof` and checked too.
- **Getters.** Getters run locally in `libemulator` on the proved state. `lite-server-get-method` asks the liteserver to run the same getter (unproved `runSmcMethod`): an independent cross-check of the proved path, never a source of data to act on.
- **Not ready.** Error 651 (the server has a block but not its shard blocks yet) is asked again for a few seconds before it is reported.

## The CHAIN protocol

Everything that talks to a live network goes through a small generic interface: `chain-pools`, `chain-ton-balance`, `chain-send`, `chain-wait-block`, `chain-emulate`, and a few more (`chain.lisp`). Message-based confirmation adds `chain-jetton-balance`, `chain-wallet-transactions` (see `transaction-matches-broadcast-p` and `external-message-normalized-hash`), and `chain-drain-flow-events` (the confirmed-flow scanner’s events, advisory). None of it knows any DEX.

`tonlib-chain` is the real implementation, over a lite client (or, in tests, a JSON tonlib client); the test suite’s `fake-chain` implements the same protocol as a scripted, in-memory state machine. A `tonlib-chain` can carry a dedicated **head-poller** (its own client, polling the masterchain head on its own thread so `chain-wait-block` returns fast) and a **flow-scanner** (watching confirmed shard-block transactions against a pool list). They are independent clients, so a slow get-method never blocks block polling or scanning. A `:lite` poller or scanner starts from a copy of the main client’s proved state, not from the anchor.

## Cells and BOC (`ton-boc.lisp`)

A self-contained implementation of TON’s cell model with no network and no foreign code: immutable `builder` and `cell` objects, `store-uint`, `store-int`, and `store-ref` to build them, and `serialize-boc` and `parse-boc` for the wire format and TON’s cell hashing.

It carries an embedded self-test against known-answer vectors (`(cl-ton:run-boc-tests)`), and the test suite cross-checks it against the real fift interpreter’s kernel words when `TON_FIFT_BINARY` is available. The file can be lifted into an unrelated project that only needs a BOC codec.

## Networking: the native Lisp proxy-liteserver

Nothing talks to the public liteservers directly. `open-proxy-liteserver` (`:implementation :native`, the default) runs a Common Lisp reimplementation of TON’s `utils/proxy-liteserver`: it holds ADNL-ext sessions to the liteservers of the global config and exposes **one local endpoint** on `127.0.0.1` that clients connect to.

`:implementation :binary` supervises the released executable instead (same interface, used for A/B verification). Here’s how the native proxy routes a query:

- **Selection.** A random alive upstream that accepts the query, weighted by recent speed and failures. Upstreams that recently answered “not ready” (30 s) or are more than 10 masterchain blocks behind the best known one are avoided. A failing upstream is avoided for 10 s, doubling up to 120 s. Only 8 sessions are kept open; the rest stand by.
- **Freshness polling.** One thread per upstream asks `getMasterchainInfo` every 2 s, so every seqno is known from the start. A `waitMasterchainSeqno` prefix goes to an upstream already at or past that seqno; otherwise, it goes to the most advanced one.
- **Hedging.** If no answer arrives within an adaptive delay (1.5 × the method’s measured time + 0.3 s, 0.5–4 s), a second upstream is asked too, and the first valid answer wins. The slow attempt is never cancelled. At most 4 upstreams are tried per query, never past the 8 s query timeout.
- **Failover.** “Not ready” (651, “not in db,” or a server behind the block the client already proved) and, for block/history/library queries (`getBlockProof`, `getLibrariesWithProof`, and others), any error start the next attempt at once. Servers differ in what they can build.
- **Failures.** A dead, timed-out, or missing upstream becomes a synthesized `liteServer.error` (653 / 652 / “no liteserver”), never a dropped query. While no upstream has ever been alive, the first queries wait up to 3 s for one.

`diagnose-proxy` and `proxy-diagnostics-report` give a verdict (`ok`, `tcp-unreachable`, `handshake-rejected`, `connected-silent`, or `starting`), failures grouped by cause and stage, and per-method answer times. `diagnose-lite` runs one of each call the bot makes through the proxy against a real network and keeps real block links as test vectors.

## The fakechain (the simulated network)

`tests/fakechain.lisp` is an ADNL-ext liteserver that answers `liteServer.*` queries from **real TVM execution**:

- `sendMessage` runs the external through the emulator against the account’s state and the config.
- `runSmcMethod` runs the getter.
- `getAccountState`, `getTransactions`, `getMasterchainInfo`, and block and proof queries are served from a local chain model (accounts, lt/hash, masterchain seqno on a virtual clock).

It uses the proxy’s framing and listener code. `(start-fakechain)` plus `(fakechain-write-global-config fc path)` gives a config a client can open, directly or through the proxy.

Fault injection options include `fail-next`, `answer-delay`, `drop-externals`, `stall-p`, and `lagging-p` (a server whose shard client is behind: everything but `getMasterchainInfo` answers 651). Real accounts can be captured with `write-account-fixture` and replayed with `fakechain-load-fixture`.

### Libraries

Contracts whose code is a library cell (STON.fi v2) only execute when the emulator is given the referenced code. The fakechain keeps a library collection (`fakechain-add-library`), hands it to the emulator for every transaction and to its `runSmcMethod`, and serves `getLibraries`; `collect-library-hashes` finds the references in a cell tree.

Run the virtual clock in step with wall time (`:time-mode :realtime :tick-seconds 1`) when code under test emulates with the real clock: an account whose `last_paid` is in the future fails the storage phase.

## The JSON tonlib oracle (tests only)

`libtonlibjson` is not part of the library. `tests/tonlib-oracle.lisp` binds it through CFFI (an asynchronous client with one receive-pump thread; `tonlib-call` correlates requests by `@extra`) and implements the methods of `tonlib-json-op`, the generic function the TONLIB-* functions call for a client that is not a lite client.

It registers its entry points in `*tonlib-oracle*`. Without it, asking for the JSON tonlib signals an error saying it is a test oracle. The tests use it as a second implementation: the same reads through `libtonlibjson` and through the lite client must agree, and the typed tonlib API tests (`tests/tlapi.lisp`) check the TL schema against it.

`libtonlibjson` and the `libgcc_s.so.1` fallback live in `tests/lib/`. On the real network, tonlib’s own sync may not finish; the lite client does not depend on it.

## Testing

```lisp
(asdf:load-system :cl-ton/test)
(cl-ton/test:run-tests)
```

Network-free tests cover BOC vectors, address/coin/dict encoding, wallet signing, the TL and ADNL-ext codecs, the proof verifier and sync (including `tests/fixtures/real/`: real mainnet block links, ordinary and Simplex), the lite client against the fakechain, the execution state machine, and the JSON tonlib oracle round trips through the Lisp proxy against the fakechain (loopback only).

Native libraries are found in `TON_TRADER_LIB_DIR`, `<bin>/lib/`, `cl-ton/lib/`, and `cl-ton/tests/lib/`.

Optional legs use the **released** fift and proxy-liteserver AppImages (BOC cross-check against fift’s kernel words; A/B parity of the proxy). They are found by `bundled-env-binary` (`<bin>/env/`, `cl-ton/tests/`, `TON_FIFT_BINARY` / `TON_PROXY_LITESERVER_BINARY`, `PATH`) and probed before use. A binary that cannot start on the host is reported once and its legs skip—except under `TON_TEST_STRICT=1`, where every skip is a failure. `TON_TRADER_TEST_SLOWNESS=3` multiplies the time bounds of the timing-sensitive checks on a slow machine.

For a self-contained run, use the test build of the application (see the top-level README).

## Contact Us

- [cl-ton-devel](https://lists.sr.ht/~lisprof/cl-ton-devel) mailing list.
- [Meta Programmers](https://t.me/lispDevs) Telegram channel.

## License

cl-ton is released under the Apache License 2.0; see the [`LICENSE`](./LICENSE) file and the [official text](https://www.apache.org/licenses/LICENSE-2.0).
