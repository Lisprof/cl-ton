Real mainnet key-block links, kept as test vectors (see test-real-link-vectors in cl-ton/tests/sync.lisp).

  link-<kind>-<from-seqno>-<to-seqno>.bin   the TL encoding of a one-link liteServer.partialBlockProof
  link-<kind>-<from-seqno>-<to-seqno>.sexp  its kind (:simplex / :ordinary) and the start block (hashes in hex)

They are written by  TON_TRADER_LITE_DIAGNOSE=mainnet ./bin/tests/ton-trader-tests  into
.lite-diagnose/<network>/capture/  after the key-block walk: copy the files here.  The tests skip cleanly while
this directory has none.  TON_TRADER_REAL_VECTORS points them at another directory.
