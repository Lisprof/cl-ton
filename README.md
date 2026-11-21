# cl-ton

A TON blockchain client for Common Lisp (SBCL). It reads the chain with its own
**verifying lite client** — every answer is proved against the config's trust anchor,
over a native Lisp proxy-liteserver — and runs get-methods and dry runs in
libemulator. Around that: a Cell/BOC codec, wallet v5r1 signing, jetton support and a
generic DEX protocol. In production it is the networking and contract layer of an
automated trading system.

The only native library the library needs is `libemulator`. The JSON tonlib
(`libtonlibjson`) is kept as a **test oracle**, see [below](#the-json-tonlib-oracle-tests-only).

A second, low-level client reads the same chain straight from untrusted full nodes over
ADNL, RLDP2 and QUIC (see [below](#adnl-over-udp-the-dht-overlays-and-quic-the-low-level-client)); it is verified on the real network, but it is not yet the
path the application runs on — the lite client above still is.

**Warning** This project is under active development; please refer to the [`package.lisp`](./src/package.lisp) file to examine the interface.

## Layout

```
cl-ton/
  src/
    package.lisp          the cl-ton package and everything it exports
    errors.lisp           the TON-ERROR condition hierarchy
    ton-boc.lisp          cell/builder/BOC codec, PMAP (see "Cells and BOC")
    slice.lisp            reading a cell back out: LOAD-UINT, LOAD-REF, ...
    base64.lisp, types.lisp   base64; address, coins, message-spec, dict encoding
    tl.lisp               the TL codec and the typed tonlib API objects (validated, no JSON)
    tl-schema.lisp        GENERATED: the ton_api / lite_api / tonlib_api schemas as Lisp data (no .tl file is read)
    vm-stack.lisp         TVM stack <-> Lisp values (the stack cell libemulator takes and returns)
    json.lisp             the one place that touches JSON (libemulator results, config files)
    emulator.lisp         libemulator FFI: local get-method runs and transaction emulation
    ed25519-batch.lisp    many Ed25519 signatures at once, on ironclad's curve operations
    proof-verify.lisp     a liteserver answer against a trusted block hash (Merkle proofs, accounts, shards)
    proof.lisp            the proof an answer was verified against, kept as a typed TL object (clton.Proof)
    sync.lisp             trusted block -> newer block: validator-set signatures over block links
    adnl-ext*.lisp        ADNL-ext crypto/framing, outbound client, inbound listener
    proxy-liteserver.lisp the native Lisp proxy-liteserver (see "Networking")
    lite-client.lisp      the verifying client: sync, account state, transactions, getters, libraries
    lite-backend.lisp     the lite client behind the TONLIB-* surface
    lite-api.lisp         LITE-EXECUTE: the typed Lite API (liteServer.* in, verified liteServer.* + proof out)
    adnl-udp.lisp         ADNL over UDP: datagrams, signed packets, channels, parts, queries
    dht.lisp              the DHT client: signed nodes and values, Kademlia search, cache
    peers.lisp            liteserver candidates: UDP and TCP probes, TCP scan, score, pools; the diagnose report
    raptorq.lisp          RaptorQ FEC (RFC 6330): the code RLDP2 carries its data in (encoder, decoder)
    rldp.lisp             RLDP2: reliable queries and answers of any size over lossy datagrams (transport-neutral)
    quic.lisp             QUIC (RFC 9000/9001) and its TLS 1.3 handshake: the node's other transport,
                          on its adnl.address.quic endpoints, with the ADNL Ed25519 key as identity
    overlay-query.lisp    overlay.query to the members of a public overlay without membership:
                          the tonNode pool (transport choice RLDP2 / ADNL / QUIC), verified block
                          and proof downloads, and the block follower
    tonlib.lisp           the chain-client surface (TONLIB-ACCOUNT-STATE, TONLIB-RUN-GET-METHOD, ...),
                          keystores, retries, getters; its answers are typed tonlib_api objects
                          (ton.blockIdExt, blocks.shortTxId, raw.transaction with raw.message) read
                          through accessors (BLOCK-ID-SEQNO, SHORT-TX-LT, RAW-TX-IN-MSG, ...); the
                          seam to the test-only JSON tonlib
    wallet.lisp, jetton.lisp             wallet v5r1; TEP-74 jettons (the DEX layer lives in the trader)
    indexer.lisp          shard-prefix matching, confirmed-transaction scanning
    chain.lisp            the CHAIN protocol and its implementation
  lib/                    libemulator-linux-x86_64.so
  tests/                  the cl-ton/test system (see "Testing")
    lib/                  TEST-ONLY native code: tonlibjson-linux-x86_64.so, compat/libgcc_s.so.1
    tl-generate.lisp      the generator of src/tl-schema.lisp from tl/*.tl, and its test
    tonlib-oracle.lisp    the JSON tonlib: FFI, the TONLIB-JSON-OP methods, the JSON bridge of the typed tonlib API
    fakechain.lisp        the emulator-backed liteserver (the simulated network)
    fake-network.lisp     WITH-FAKE-NETWORK: a fakechain and a verifying client, driven by typed Lite API objects only
    fake-world.lisp       the captured DEX contracts and jetton wallets loaded into a fake network
    scenario-kit.lisp     wallet sends, jetton transfers, balances: a scenario in a few lines
    api.lisp              LITE-EXECUTE against real tonlib, its proofs and forged proofs; the verdict channel
    fixtures/             captured real data (real/: mainnet block links, dex/: captured contracts)
    fift-linux-x86_64, proxy-liteserver-linux-x86_64   the released executables (A/B reference)
  cl-ton.asd
```

Two ASDF systems: `cl-ton` (the library) and `cl-ton/test`. `files.lisp` and
`fakechain.lisp` live under `tests/` but are components of the test system, which
also loads the JSON tonlib oracle first.

## The lite client

`open-lite-client` (normally reached through the TONLIB-* surface) trusts exactly one thing:
the `init_block` of the global config. From it:

- **Key-block chain.** It walks block proofs forward to the newest key block, checking each
  link's validator signatures against the validator set the previous key block committed
  to (ordinary and Simplex signature sets, weighted, two thirds required). The newest
  proved key block is kept in a state file in the keystore (checksum, owner and mode
  checked, bound to the anchor), so only the first start walks the whole chain (minutes
  on a weak link; later starts take seconds).
- **Heads and pinned reads.** `lite-sync` proves the newest masterchain head from the
  stored key block. Reads can be pinned to a block with `*get-method-block*`; the pool
  reads of a bot run in `PMAP` worker threads, so any special that must reach workers is
  listed in `*pmap-conveyed*`.
- **Proved reads.** Account states, shards, block transactions and account transactions
  come with Merkle proofs checked against the proved block; the public libraries a
  contract refers to (STON.fi v2 keeps pool code in libraries) are fetched with
  `getLibrariesWithProof` and checked too.
- **Getters** run locally in libemulator on the proved state. `lite-server-get-method` asks
  the liteserver to run the same getter (unproved `runSmcMethod`): an independent
  cross-check of the proved path, never a source of data to act on.
- **Not ready.** Error 651 (the server has a block but not its shard blocks yet) is asked
  again for a few seconds before it is reported.

## The CHAIN protocol

Everything that talks to a live network goes through a small interface, a `chain` structure whose slots hold one function per operation (an implementation fills them in; no generic dispatch) —
`chain-pools`, `chain-ton-balance`, `chain-send`, `chain-wait-block`, `chain-emulate` and
a few more (`chain.lisp`). Message-based confirmation adds `chain-jetton-balance`,
`chain-wallet-transactions` (see `transaction-matches-broadcast-p` and
`external-message-normalized-hash`) and `chain-drain-flow-events` (the confirmed-flow
scanner's events, advisory). `emulator.lisp` decodes the outbound messages of an emulated
transaction (`emulation-out-messages-summary`, `parse-message-summary`, `dict-entries`).
None of it knows any DEX.

`tonlib-chain` is the real implementation, over a lite client (or, in tests, a JSON tonlib
client); the test suite's `fake-chain` implements the same protocol as a scripted,
in-memory state machine. A `tonlib-chain` can carry a dedicated **head-poller** (its own
client, polling the masterchain head on its own thread so `chain-wait-block` returns fast)
and a **flow-scanner** (watching confirmed shard-block transactions against a pool list).
They are independent clients, so a slow get-method never blocks block polling or
scanning. A `:lite` poller or scanner starts from a copy of the main client's proved
state, not from the anchor.

## Cells and BOC (`ton-boc.lisp`)

A self-contained implementation of TON's cell model with no network and no foreign code:
immutable `builder`/`cell` objects, `store-uint`/`store-int`/`store-ref` to build them,
`serialize-boc`/`parse-boc` for the wire format and TON's cell hashing. It carries an
embedded self-test against known-answer vectors (`(cl-ton:run-boc-tests)`), and the test
suite cross-checks it against the real fift interpreter's kernel words when
`TON_FIFT_BINARY` is available. The file can be lifted into an unrelated project that
only needs a BOC codec.

## Networking: the native Lisp proxy-liteserver

Nothing talks to the public liteservers directly. `open-proxy-liteserver`
(`:implementation :native`, the default) runs a Common Lisp reimplementation of TON's
`utils/proxy-liteserver`: it holds ADNL-ext sessions to the liteservers of the global
config and exposes ONE local endpoint on `127.0.0.1` that clients connect to.
`:implementation :binary` supervises the released executable instead (same interface, used
for A/B verification). How the native proxy routes a query:

- **Selection.** A random alive upstream that accepts the query, weighted by recent speed and
  failures; upstreams that recently answered "not ready" (30 s) or are more than 10
  masterchain blocks behind the best known one are avoided; a failing upstream is avoided
  for 10 s, doubling up to 120 s. Only 8 sessions are kept open, the rest stand by.
- **Freshness polling.** One thread per upstream asks `getMasterchainInfo` every 2 s, so every
  seqno is known from the start. A `waitMasterchainSeqno` prefix goes to an upstream
  already at or past that seqno, else to the most advanced one.
- **Hedging.** If no answer arrives within an adaptive delay (1.5 x the method's measured time
  + 0.3 s, 0.5-4 s), a second upstream is asked too and the first valid answer wins; the slow
  attempt is never cancelled. At most 4 upstreams per query, never past the 8 s query timeout.
- **Failover.** "Not ready" (651, "not in db", a server behind the block the client already
  proved) and, for block/history/library queries (`getBlockProof`, `getLibrariesWithProof`,
  ...), any error, start the next attempt at once. Servers differ in what they can build.
- **Failures.** A dead, timed-out or missing upstream becomes a synthesized `liteServer.error`
  (653 / 652 / "no liteserver"), never a dropped query. While no upstream has ever been alive
  the first queries wait up to 3 s for one.

`diagnose-proxy` and `proxy-diagnostics-report` give a verdict (`ok`, `tcp-unreachable`,
`handshake-rejected`, `connected-silent`, `starting`), the failures grouped by cause and
stage, and per-method answer times. `diagnose-lite` runs one of each call the bot makes
through the proxy against a real network and keeps real block links as test vectors.

## The typed Lite API

`(lite-execute client request)` is the one interface the application and its tests use to read
the chain. REQUEST is a typed lite API function object (`(tl-make "liteServer.getAccountState"
...)`, schema `lite_api.tl`); it returns `(values answer proof)`: ANSWER is the typed lite
API object a liteserver answers with, but only after the lite client verified it against the
chain it trusts, and PROOF is the `clton.proof*` object it verified (`verify-proof` checks it
again; it survives its TL bytes), or NIL where an answer carries none (what a server says of
itself: `getTime`, `getVersion`, the version and clock of `getMasterchainInfoExt`).

Functions: `getMasterchainInfo`, `getMasterchainInfoExt`, `getTime`, `getVersion`,
`getAccountState` (any block of the trusted chain), `getTransactions`, `getOneTransaction`,
`runSmcMethod` (run by the client's own emulator on the PROVED state, config and libraries,
never the server's word), `getBlock`, `getBlockHeader`, `lookupBlock`, `getBlockProof`,
`getShardBlockProof`, `getAllShardsInfo`, `getShardInfo`, `getConfigAll`, `getConfigParams`,
`listBlockTransactions`, `listBlockTransactionsExt`, `getLibraries`, `getLibrariesWithProof`,
`sendMessage` (refuses what is not an inbound external message before sending; status 1 is
acceptance into the pool, not inclusion). `(lite-execute-supported)` lists them. Anything else
signals. The keyword `:min-seqno` enforces a freshness floor: the request runs only once the head
the client PROVED is at or above that masterchain seqno. Add a function with `def-lite-function`.

## The fakechain (the simulated network)

`tests/fakechain.lisp` is an ADNL-ext liteserver that answers `liteServer.*` queries from
REAL TVM execution: `sendMessage` runs the external through the emulator against the
account's state and the config, `runSmcMethod` runs the getter, and `getAccountState` /
`getTransactions` / `getMasterchainInfo` / block and proof queries are served from a local
chain model (accounts, lt/hash, masterchain seqno on a virtual clock). It uses the proxy's
framing and listener code. `(start-fakechain)` + `(fakechain-write-global-config fc path)`
gives a config a client can open, directly or through the proxy. Fault injection:
`fail-next`, `answer-delay`, `drop-externals`, `stall-p`, `lagging-p` (a server whose shard
client is behind: everything but `getMasterchainInfo` answers 651). Real accounts are
captured with `write-account-fixture` and replayed with `fakechain-load-fixture`.

**Libraries.** Contracts whose code is a library cell (STON.fi v2) only execute when the
emulator is given the referenced code. The fakechain keeps a library collection
(`fakechain-add-library`), hands it to the emulator for every transaction and to its
`runSmcMethod`, and serves `getLibraries`; `collect-library-hashes` finds the references in
a cell tree. Run the virtual clock in step with wall time (`:time-mode :realtime
:tick-seconds 1`) when code under test emulates with the real clock: an account whose
`last_paid` is in the future fails the storage phase.

**The masterchain.** Accounts of workchain -1 live next to those of workchain 0 (the table key carries an
offset): messages execute for both and cross between them, masterchain transactions go into the
masterchain block, and a masterchain account is proved in the masterchain block itself.
Outgoing external messages are not delivered anywhere, as on the real network;
`(fakechain-external-outs fc)` lists them for a test.

**The fake network, the fake world, the scenario kit.** A test does not start a fakechain, a client or a
proxy by hand: `(with-fake-network (net :blocks 2) ...)` gives a running fakechain and a verifying client;
`(fnet-execute net request)` is `lite-execute` on it, `(fnet-advance net n)` seals blocks (time passes only
then), `(fnet-fund-wallet net)` deploys a funded wallet. `(fnet-load-dex-world net)` seeds the captured DEX
contracts (STON.fi v1/v2, DeDust, jetton masters, pTON; `$TON_TRADER_DEX_FIXTURES` or
`<project>/tests/fixtures/dex/`) at their real addresses, `(fnet-deploy-jetton-wallet net master owner
amount)` gives an owner jettons, and the scenario kit sends messages (`fnet-wallet-send`,
`fnet-send-jettons`) and reads results back (`fnet-balance`, `fnet-jetton-balance`, `fnet-get-method`).
A seeded account is provable once a block is sealed; the loaders seal one themselves.

## ADNL over UDP, the DHT, overlays and QUIC (the low-level client)

`adnl-udp.lisp` speaks ADNL over UDP as the node does (signed packets encrypted to the peer's key, channels, parts, replay
rules; `adnl-udp-query`), `dht.lisp` is a DHT client on it (bare queries, every node and value checked against its signatures,
Kademlia search, `dht-find-address` for the address record of an ADNL id, a cache file; the sixteen mainnet DHT nodes of the global config are the only
static seed) and `peers.lisp` evaluates the nodes found as liteserver candidates (probes with `liteServer.getTime` and
`getMasterchainInfo` over UDP and over ADNL ext TCP, a TCP port scan of the hosts of the DHT nodes that answered, a score of round
trip, blocks behind the head and failures, hot and warm pools; `dht-diagnose` runs the crawl, the scan and the probes and prints a
report). The DHT publishes only the UDP address and the ADNL key of a node, not a liteserver's TCP port or key, which is why the scan
exists.

On top of ADNL-UDP sit RLDP2 (`rldp.lisp`: reliable query delivery with RaptorQ forward error correction, `raptorq.lisp`) and the
overlay client (`overlay-query.lisp`). It discovers the members of a public overlay through the DHT — no overlay membership —
and asks them `tonNode.*` queries over ADNL, RLDP2 or QUIC, pooled with staggered hedging. Nothing a peer answers is believed
before it verifies: a downloaded block is checked against the block id it was asked for, and the **follower** (`tonnode-follower`)
walks the masterchain and its shards from a key block proved against the `init_block` anchor, so account state is read against a
state root the follower itself proved. Watchlist reads are served from the followed state, cold reads are proved against the
follower's shard state hash, and get-methods run at a caller-trusted block on the proved state in libemulator. External messages
leave as overlay broadcasts. The whole path is exercised on the real mainnet: DHT bootstrap, overlay discovery, a
`tonNode.getCapabilities` answer, the pinned init block downloaded from untrusted peers and verified, and the follower advancing
past the head the lite client reported. The client stays light: it follows blocks and checks proofs, it never downloads the
network's state.

`quic.lisp` is a QUIC transport (RFC 9000/9001) for the same overlay queries: TLS 1.3 with the node's ADNL Ed25519 key as a raw
public key (RFC 7250), SNI `<adnl-id-hex>.adnl`, ALPN `ton`, endpoints taken from the signed `adnl.address.quic` records. It is
verified end to end against the genuine validator-engine (ngtcp2/OpenSSL) on a private network built with the application's
`tools/local-net`: the stateless Retry handshake with client certificate, `tonNode.getCapabilities`, a proved key block downloaded
through a QUIC pool, and follower steps over QUIC. Public mainnet nodes advertise QUIC endpoints in quantity, but they do not
answer an arbitrary internet peer — an independent QUIC implementation sees the same silence — so on mainnet RLDP2 remains the
working transport, and QUIC serves where a node is known to answer.

None of this is wired into the lite client: the two paths are separate. The planned next stage is a backend that serves the
TONLIB-* surface from the low-level client, so the application can move from the lite protocol to the `ton_api` path without
changing its calls.

## The JSON tonlib oracle (tests only)

`libtonlibjson` is not part of the library. `tests/tonlib-oracle.lisp` binds it through
CFFI (an asynchronous client with one receive pump thread; `tonlib-call` correlates
requests by `@extra`) and implements the methods of `tonlib-json-op`, the generic function the
TONLIB-* functions call for a client that is not a lite client. It registers its entry points
in `*tonlib-oracle*`. Its requests are typed tonlib API objects turned into JSON for
`libtonlibjson`, and its answers are turned back into the same typed objects (`json->tlapi`), so
the lite client's and the oracle's answers are compared as typed objects. Without it, asking for the JSON tonlib signals an
error that says it is a test oracle. The tests use it as a second implementation: the same
reads through `libtonlibjson` and through the lite client must agree, and the typed
tonlib API tests (`tests/tlapi.lisp`) check the TL schema against it; `lite-execute` is compared with it
(`tests/api.lisp`). `libtonlibjson` and
the `libgcc_s.so.1` fallback live in `tests/lib/`. On the real network tonlib's own sync
may not finish; the lite client does not depend on it.

## Testing

```lisp
(asdf:load-system :cl-ton/test)
(cl-ton/test:run-tests)
```

Network-free: BOC vectors, address/coin/dict encoding, wallet signing, the TL and ADNL-ext
codecs, the QUIC packet layer and TLS 1.3 handshake against the RFC 9001/8448 vectors and a mock server,
the proof verifier and the sync (including `tests/fixtures/real/`: real mainnet
block links, ordinary and Simplex), the lite client against the fakechain, the execution
state machine, and the JSON tonlib oracle round trips through the Lisp proxy against the
fakechain (loopback only). Native libraries are found in `TON_TRADER_LIB_DIR`, `<bin>/lib/`,
`cl-ton/lib/` and `cl-ton/tests/lib/`.

Optional legs use the **released** `fift` and `proxy-liteserver` AppImages (BOC cross-check
against fift's kernel words; A/B parity of the proxy). They are found by
`bundled-env-binary` (`<bin>/env/`, `cl-ton/tests/`, `TON_FIFT_BINARY` /
`TON_PROXY_LITESERVER_BINARY`, `PATH`) and probed before use. A binary that cannot start on
the host is reported once and its legs skip — except under `TON_TEST_STRICT=1`, where
every skip is a failure. `TON_TRADER_TEST_SLOWNESS=3` multiplies the time bounds of the
timing-sensitive checks on a slow machine. For a self-contained run use the test build of
the application (see the top-level README).

## Contact Us

- **[cl-ton-devel](https://lists.sr.ht/~lisprof/cl-ton-devel)** mailing list.
- **[Meta Programmers](https://t.me/lispDevs)** Telegram channel.

## License

cl-ton is released under the Apache License 2.0; see the [LICENSE](./LICENSE) file and the [official text](https://www.apache.org/licenses/LICENSE-2.0).
