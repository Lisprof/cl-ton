# cl-ton

A TON blockchain proxy-liteserver/client for Common Lisp (SBCL). proxy-liteserver, Cell/BOC codec, tonlib and local-emulator bindings, wallet v5r1 signing, jetton support, and a generic DEX protocol. General-purpose TON client functionality; in production use as the networking and contract layer of an automated trading system.

### Warning

This project is under active development; please refer to the [`package.lisp`](https://git.sr.ht/~lisprof/cl-ton/tree/main/item/src/package.lisp) file to examine the interface.

# Layout

```text
cl-ton/
  src/
    ton-boc.lisp         cell/builder/BOC codec (own section below)
    slice.lisp           reading a cell back out: LOAD-UINT, LOAD-REF, ...
    types.lisp           address, coins, message-spec, dict encoding
    base64.lisp          standard + URL-safe base64
    tl.lisp              TL codec + the lite_api / ton_api schema subset (constructor ids = CRC32)
    wallet.lisp          mnemonic -> keypair, wallet v5r1, external messages
    chain.lisp           the CHAIN protocol (see below) + its tonlib client
    tonlib.lisp          tonlibjson FFI: get-methods, sending, block/tx queries
    emulator.lisp        libemulator FFI: local dry runs, no network needed
    indexer.lisp         shard-prefix matching, confirmed-transaction scanning
    jetton.lisp          TEP-74 jetton wallet discovery + transfer bodies
    vm-stack.lisp        tonlib's JSON stack format <-> Lisp values
    dex.lisp             generic DEX protocol (defgenerics only, no contracts)
    adnl-ext.lisp        ADNL-ext crypto + framing (AES-256-CTR streams, init packet)
    adnl-ext-client.lisp outbound liteserver session (reconnect loop, query table)
    adnl-ext-server.lisp inbound listener/handshake, shared by the proxy and the fakechain
    proxy-liteserver.lisp  the native Lisp proxy-liteserver (see "Networking")
    errors.lisp          the TON-ERROR condition hierarchy
    package.lisp         the cl-ton package and everything it exports
  lib/                   tonlibjson + libemulator shared libraries (checkout location)
  tests/
    client.lisp          RUN-TESTS and the network-free tests (BOC/address/wallet vectors)
    files.lisp           BUNDLED-ENV-BINARY (loaded by the library, see cl-ton.asd)
    fakechain.lisp       the emulator-backed fakechain liteserver (loaded by the library, see cl-ton.asd)
    fake-chain.lisp      execution-state-machine tests on a scripted CHAIN
    tl-adnl-ext.lisp     TL / ADNL-ext codec tests
    proxy-ext.lisp       native proxy tests against scripted upstreams
    scenarios.lisp       tonlib -> proxy -> fakechain scenarios, fault injection, A/B legs
    compat/              libgcc_s.so.1 fallback for the released binaries (see Testing)
    fift-linux-x86_64, proxy-liteserver-linux-x86_64
                         the released fift / proxy-liteserver AppImages (A/B reference)
  cl-ton.asd
```

Two ASDF systems: `cl-ton` (the library) and `cl-ton/test` (tests: network-free, or loopback-only against the fakechain – see <span class="spurious-link" target="*Testing">*Testing*</span>). `files.lisp` and `fakechain.lisp` live under `tests/` but are components of the library system (`:pathname "../tests/..."` in `cl-ton.asd`).

# The CHAIN protocol

Everything that talks to a live network goes through a small generic interface — `chain-pools`, `chain-ton-balance`, `chain-send`, `chain-wait-block`, `chain-emulate`, and a handful more (see `chain.lisp`). Message-based confirmation uses three more, all blockchain-generic: `chain-jetton-balance` (the wallet's balance of any jetton master), `chain-wallet-transactions` (raw transactions, newest first — see `transaction-matches-broadcast-p` and `external-message-normalized-hash` for recognising the one that consumed a broadcast) and `chain-drain-flow-events` (the confirmed-flow scanner's events, advisory). `emulator.lisp` also decodes a transaction's outbound messages (`emulation-out-messages-summary`, `parse-message-summary`, `dict-entries`) so callers can inspect what an emulated external message would send. None of it knows any DEX. `tonlib-chain` is the real implementation, backed by a tonlibjson client; the test suite's `fake-chain` implements the same protocol as a scripted, in-memory state machine, so higher-level logic can be tested without a network. Anything built against `CHAIN` works against either.

A `tonlib-chain` can optionally carry a dedicated **head-poller** (its own tonlib client, polling `blocks.getMasterchainInfo` on its own thread so `chain-wait-block` returns fast) and a dedicated **flow-scanner** (another client, watching confirmed shard-block transactions against a configured pool-address list). Both are independent tonlib clients, so a slow or stuck get-method call never blocks block-polling or flow-scanning and vice versa.

# Cell hashing and BOC serialization (`ton-boc.lisp`)

This is the one piece of cl-ton with no external dependency at all — no CFFI, no network — a self-contained implementation of TON's cell model: immutable `builder~/~cell` objects, `STORE-UINT~/~STORE-INT~/~STORE-REF~/...  
to build one, ~SERIALIZE-BOC~/~PARSE-BOC` for the wire format, and standard cell hashing (SHA-256 over each cell's descriptor bytes + data + children's hashes, recursively, matching TON's own algorithm).

It carries a large embedded self-test against a bundled `vectors.json` of known-answer BOC/hash vectors (`(cl-ton:run-boc-tests)`), and the test suite additionally cross-checks it against the real fift interpreter's own kernel words (`<b`, `u,`, `i,`, `ref,`, `b>`, `hash`, `boc+>B`) when `TON_FIFT_BINARY` is set — the reference implementation itself, not a second implementation of the same algorithm. See <span class="spurious-link" target="*Testing">*Testing*</span>.

The file is self-contained enough to lift into an unrelated project if you only need a BOC codec.

# Networking: the native Lisp proxy-liteserver

`tonlibjson.so` never talks to the public liteservers directly. `open-proxy-liteserver` (`:implementation :native`, the default) runs a Common Lisp reimplementation of TON's `utils/proxy-liteserver`: it holds ADNL-ext sessions to every liteserver in the global config and exposes ONE local endpoint, `127.0.0.1`, that tonlib connects to (`open-tonlib-via-proxy` writes the routed config: exactly one liteserver entry, the proxy). `:implementation :binary` supervises the released executable instead (same interface, used for A/B verification). How the native proxy routes a query:

- **Selection.** A random alive upstream that accepts the query (slice restrictions honoured), except that upstreams which recently answered "not ready" are avoided (`*proxy-lagging-penalty*`, 30 s) and upstreams more than `*proxy-max-lag*` (10) masterchain blocks behind the best known one are avoided too.
- **Freshness polling.** One thread per upstream asks `getMasterchainInfo` every `*proxy-poll-interval*` (2 s), so every upstream's seqno is known from the start, not only after clients happened to ask it. Public liteservers include stale ones; a stale one asked to wait for a new block holds the client until its timeout (a tonlib request that "timed out after 120 s"), and gives old data or short block-proof chains otherwise.
- **Waits.** A `waitMasterchainSeqno` prefix goes to an upstream already at or past that seqno (prefix dropped, it answers at once), else to the most advanced upstream, with the remaining timeout.
- **Failover.** An upstream answering liteServer error 651 ("not ready": the block or state is not in ITS database, e.g. a shard client that is behind) is penalized and the query retried on the next upstream; only if none is left is that answer passed through.
- **Failures.** A dead, timed-out or missing upstream becomes a synthesized `liteServer.error` (653 / 652 / "no liteserver"), never a dropped query; the texts and codes match the released binary. While no upstream has ever been alive (the proxy listens before its sessions are up) the first queries wait up to `*proxy-startup-grace*` (3 s) for one.

# The fakechain (the simulated network)

`tests/fakechain.lisp` is an ADNL-ext liteserver that answers `liteServer.*` queries from REAL TVM execution: `sendMessage` runs the external through the emulator against the account's state and the config cell, `runSmcMethod` runs the getter, and `getAccountState` / `getTransactions` / `getMasterchainInfo` / block queries are served from a local chain model (accounts, lt/hash, masterchain seqno on a virtual clock) whose transitions are produced by the emulator. It uses the same framing and listener code as the proxy. `(start-fakechain)` + `(fakechain-write-global-config fc path)` gives a config real tonlib can open, directly or through the proxy. Fault injection: `fail-next`, `answer-delay`, `drop-externals`, `stall-p`, `lagging-p` (a server whose shard client is behind: every query but `getMasterchainInfo` gets error 651). Real accounts can be captured with `write-account-fixture` and replayed with `fakechain-load-fixture`.

### Libraries

Contracts whose code, or whose deployed children's code, is a library cell (STON.fi v2 keeps its pool / LP-account / vault code that way: the router's data cell holds four library references) only execute when the emulator is given the referenced code.

The fakechain keeps a library collection (~fakechain-add-library~), hands it to the emulator for every transaction and serves the plain ~liteServer.getLibraries~ to direct ADNL clients.

Limit: tonlib itself fetches libraries with a proof-checked query (~getLibrariesWithProof~) that only a real liteserver can answer, so tonlib-side get-methods on library-coded contracts are not verified against the fakechain. ~collect-library-hashes~ finds the references in a cell tree; fixtures carry the libraries their account references.

Run the virtual clock in step with wall time (`:time-mode :realtime :tick-seconds 1`) when code under test emulates locally with the real clock: an account whose `last_paid` is in the future fails the storage phase.

# Testing

``` commonlisp
(asdf:load-system :cl-ton/test)
(cl-ton/test:run-tests)
```

Network-free: BOC vectors, address/coin/dict encoding, wallet signing, tonlib response dispatch, the execution state machine, the TL / ADNL-ext codecs, and real tonlib round trips through the Lisp proxy against the emulator-backed fakechain (loopback only; needs `tonlibjson` and `libemulator` in `cl-ton/lib/`, or `TON_TRADER_LIB_DIR`).

Optional legs use the **released** executables (`fift`, `proxy-liteserver`; AppImages): the BOC cross-check against fift's own kernel words, and the A/B parity legs that run the same scenarios through the released proxy. They are found by `BUNDLED-ENV-BINARY` (`<bin>/env/`, `cl-ton/tests/`, `TON_FIFT_BINARY` / `TON_PROXY_LITESERVER_BINARY`, `PATH`) and are probed before use. A binary that cannot start on the host (missing `libgcc_s.so.1`, no FUSE for the AppImage) is reported once and its legs skip, they do not fail – except under `TON_TEST_STRICT=1`, where every skip is a failure. The fift cross-check needs no `Fift.fif~/~Asm.fif`, only fift's built-in kernel words.

For a self-contained run use the test build of the application (see the top-level README): `sbcl --script builder.lisp --with-tests` then `bin/tests/run-tests.sh` – the AppImages are extracted there, so FUSE is not needed, and `compat/libgcc_s.so.1` is used when the host has none.

# Contact Us

[cl-ton-devel](https://lists.sr.ht/~lisprof/cl-ton-devel) mailing list.

[Meta Programmers](https://t.me/lispDevs) Telegram channel.

# License

cl-ton is released under the Apache License 2.0; see the `LICENSE` file and the official text at <https://www.apache.org/licenses/LICENSE-2.0>.
