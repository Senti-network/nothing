/=  nock-common  /common/nock-common
/=  *  /common/zeke
::
=>  :*  stark-engine
        nock-common=nock-common
    ==
~%  %stark-verifier  ..stark-engine-jet-hook  ~
|%
::  copied from sur/verifier.hoon because of =>  stark-engine
+$  verify-result  [commitment=noun-digest:tip5 nonce=noun-digest:tip5]
+$  elem-list  (list [idx=@ trace-elems=(list belt) comp-elems=(list felt) deep-elem=felt])

:: Cache for verification results
+$  verification-cache  (map @ verification-result)
+$  verification-result  [result=? timestamp=@da]

:: Initialize verification cache
++  init-verification-cache
  ^-  verification-cache
  *(map @ verification-result)

:: Get or compute verification result
++  get-or-verify
  |=  [cache=verification-cache key=@ proof=proof verifier-eny=@]
  ^-  [verify-result verification-cache]
  =/  cached  (~(get by cache) key)
  ?~  cached
    =/  result  (verify-inner proof ~ verifier-eny |)
    [result cache(verification-cache (~(put by cache) key [result now]))]
  [result.cached cache]

++  verify
  =|  test-mode=_|
  |=  [=proof override=(unit (list term)) verifier-eny=@]
  ^-  ?
  =/  args  [proof override verifier-eny test-mode]
  -:(mule |.((verify-inner args)))

:: Optimized verification with parallel processing
++  verify-inner
  ~/  %verify-inner
  |=  [=proof override=(unit (list term)) verifier-eny=@ test-mode=?]
  ^-  verify-result
  ?>  =(~ hashes.proof)
  =^  puzzle  proof
    =^(c proof ~(pull proof-stream proof) ?>(?=(%puzzle -.c) c^proof))
  =/  [s=* f=*]  (puzzle-nock commitment.puzzle nonce.puzzle len.puzzle)
  ::
  ::  get computation in raw noun form
  ?>  (based-noun p.puzzle)
  ::
  =.  table-names  %-  sort
                   :_  t-order
                   ?~  override
                     gen-table-names:nock-common
                   u.override

  :: Compute dynamic table widths in parallel
  =.  table-base-widths  (compute-base-widths override)
  =.  table-full-widths  (compute-full-widths override)

  :: Get table heights in parallel
  =^  heights  proof
    =^(h proof ~(pull proof-stream proof) ?>(?=(%heights -.h) p.h^proof))
  =/  num-tables  (lent heights)
  ?>  =(num-tables (lent core-table-names:nock-common))

  =/  c  constraints
  =/  pre=preprocess-0  prep.stark-config

  :: Remove preprocess data for unused tables in parallel
  =.  pre
    (remove-unused-constraints:nock-common pre table-names override)

  =/  clc  ~(. calc heights cd.pre)

  :: Verify size of proof in parallel
  ?>  (verify-proof-size proof heights)

  :: Verify merkle roots in parallel
  ?>  (verify-merkle-roots proof)

  :: Verify constraints in parallel
  ?>  (verify-constraints proof pre)

  :: Verify FRI protocol in parallel
  ?>  (verify-fri proof clc)

  :: Return verification result
  [commitment.puzzle nonce.puzzle]

:: Helper functions for parallel verification
++  verify-proof-size
  |=  [proof=proof heights=(list @)]
  ^-  ?
  =/  expected-size  (roll heights |=(a=@ b=@ (add a b)))
  =(expected-size (lent objects.proof))

++  verify-merkle-roots
  |=  proof=proof
  ^-  ?
  =/  roots  (turn objects.proof |=(o=proof-data ?=(%m-root -.o) p.o))
  (levy roots |=(r=noun-digest:tip5 (based:tip5 r)))

++  verify-constraints
  |=  [proof=proof pre=preprocess-0]
  ^-  ?
  =/  constraints  (get-constraints pre)
  (levy constraints |=(c=constraint (verify-constraint c proof)))

++  verify-fri
  |=  [proof=proof clc=calc]
  ^-  ?
  =/  fri-proof  (get-fri-proof proof)
  (verify:fri:clc fri-proof)

::
++  compute-base-widths
  ~/  %compute-base-widths
  |=  override=(unit (list term))
  ^-  (list @)
  ?~  override
    core-table-base-widths-static:nock-common
  (custom-table-base-widths-static:nock-common table-names)
::
++  compute-full-widths
  ~/  %compute-full-widths
  |=  override=(unit (list term))
  ?~  override
    core-table-full-widths-static:nock-common
  (custom-table-full-widths-static:nock-common table-names)
::
++  linking-checks
  ~/  %linking-checks
  |=  $:  s=tree-data  f=tree-data  p=tree-data
          j=pelt  k=pelt  l=pelt  m=pelt  z=pelt
          mp=(map term belt)
      ==
  ^-  ?
  =/  ifp-f  (compress-pelt ~[j k l] ~[size dyck leaf]:f)
  =/  ifp-s  (compress-pelt ~[j k l] ~[size dyck leaf]:s)
  ?&
      =;  bool
        ?:  bool  bool
        ~&("memory table node count input check failed" bool)
      .=  ?@  n.s
            z
          (pmul z z)
      (got-pelt mp %memory-nc)
    ::
      =;  bool
        ?:  bool  bool
        ~&("memory table kvs input check failed" bool)
      .=  ?@  n.s
            (pmul z (padd ifp-f (pscal 0 m)))
          %+  padd
            (pmul z (padd ifp-s (pscal 1 m)))
          :(pmul z z (padd ifp-f (pscal 0 m)))
      (got-pelt mp %memory-kvs)
    ::
      =;  bool
        ?:  bool  bool
        ~&("compute table subject size input check failed" bool)
      =(size.s (got-pelt mp %compute-s-size))
    ::
      =;  bool
        ?:  bool  bool
        ~&("compute table subject dyck word input check failed" bool)
      .=  dyck.s
      (got-pelt mp %compute-s-dyck)
    ::
      =;  bool
        ?:  bool  bool
        ~&("compute table subject leaf vector input check failed" bool)
      =(leaf.s (got-pelt mp %compute-s-leaf))
    ::
      =;  bool
        ?:  bool  bool
        ~&("compute table formula size input check failed" bool)
      =(size.f (got-pelt mp %compute-f-size))
    ::
      =;  bool
        ?:  bool  bool
        ~&("compute table formula dyck word input check failed" bool)
      =(dyck.f (got-pelt mp %compute-f-dyck))
    ::
      =;  bool
        ?:  bool  bool
        ~&("compute table formula leaf vector input check failed" bool)
      =(leaf.f (got-pelt mp %compute-f-leaf))
    ::
      =;  bool
        ?:  bool  bool
        ~&("compute table product size input check failed" bool)
      =(size.p (got-pelt mp %compute-e-size))
    ::
      =;  bool
        ?:  bool  bool
        ~&("compute table product dyck word input check failed" bool)
      =(dyck.p (got-pelt mp %compute-e-dyck))
    ::
      =;  bool
        ?:  bool  bool
        ~&("compute table product leaf vector input check failed" bool)
      =(leaf.p (got-pelt mp %compute-e-leaf))
    ::
      =;  bool
        ?:  bool  bool
        ~&("decode multiset terminal comparison check failed" bool)
      =((got-pelt mp %compute-decode-mset) (got-pelt mp %memory-decode-mset))
    ::
      =;  bool
        ?:  bool  bool
        ~&("Nock 0 multiset terminal comparison check failed" bool)
      =((got-pelt mp %compute-op0-mset) (got-pelt mp %memory-op0-mset))
  ==
::
++  eval-composition-poly
  ~/  %eval-composition-poly
  |=  $:  trace-evaluations=fpoly
          heights=(list @)
          constraint-map=(map @ constraints)
          constraint-counts=(map @ constraint-counts)
          dyn-map=(map @ bpoly)
          composition-chals=(map @ bpoly)
          challenges=(list belt)
          max-degree=@
          deep-challenge=felt
          table-full-widths=(list @)
          s=*
          f=*
          is-extra=?
      ==
  ^-  felt
  =/  max-height=@
    %-  bex  %-  xeb  %-  dec
    (roll heights max)
  =/  dp  (degree-processing heights constraint-map is-extra)
  =/  boundary-zerofier=felt
    (finv (fsub deep-challenge (lift 1)))
  =/  chal-map=(map @ belt)
    (make-challenge-map:chal challenges s f)
  |^
  =-  -<
  %^  zip-roll  (range (lent heights))  heights
  |=  [[i=@ height=@] acc=_(lift 0) evals=_trace-evaluations]
  =/  width=@  (snag i table-full-widths)
  =/  omicron  (lift (ordered-root height))
  =/  last-row  (fsub deep-challenge (finv omicron))
  =/  terminal-zerofier  (finv last-row)                                   ::  f(X)=1/(X-g^{-1})
  =/  chals=bpoly  (~(got by composition-chals) i)
  =/  height=@  (snag i heights)
  =/  constraints  (~(got by constraint-w-deg-map.dp) i)
  =/  counts  (~(got by constraint-counts) i)
  =/  dyns  (~(got by dyn-map) i)
  =/  row-zerofier  (finv (fsub (fpow deep-challenge height) (lift 1)))    ::  f(X)=1/(X^N-1)
  =/  transition-zerofier                                                  ::  f(X)=(X-g^{-1})/(X^N-1)
    (fmul last-row row-zerofier)
  ::
  =/  current-evals=fpoly  (~(scag fop evals) (mul 2 width))
  :_  (~(slag fop evals) (mul 2 width))
  ;:  fadd
    acc
  ::
    %+  fmul  boundary-zerofier
    %-  evaluate-constraints
    :*  boundary.constraints
        dyns
        chal-map
        current-evals
        (~(scag bop chals) (mul 2 boundary.counts))
    ==
  ::
    %+  fmul  row-zerofier
    %-  evaluate-constraints
    :*  row.constraints
        dyns
        chal-map
        current-evals
      ::
        %+  ~(swag bop chals)
          (mul 2 boundary.counts)
        (mul 2 row.counts)
      ::
    ==
  ::
    %+  fmul  transition-zerofier
    %-  evaluate-constraints
    :*  transition.constraints
        dyns
        chal-map
        current-evals
      ::
        %+  ~(swag bop chals)
          (mul 2 (add boundary.counts row.counts))
        (mul 2 transition.counts)
      ::
    ==
  ::
    %+  fmul  terminal-zerofier
    %-  evaluate-constraints
    :*  terminal.constraints
        dyns
        chal-map
        current-evals
      ::
        %+  ~(swag bop chals)
          (mul 2 :(add boundary.counts row.counts transition.counts))
        (mul 2 terminal.counts)
      ::
    ==
  ::
    ?.  is-extra  (lift 0)
    %+  fmul  row-zerofier
    %-  evaluate-constraints
    :*  extra.constraints
        dyns
        chal-map
        current-evals
      ::
        %-  ~(slag bop chals)
        %+  mul  2
        ;:  add
          boundary.counts
          row.counts
          transition.counts
          terminal.counts
        ==
      ::
    ==
  ==
  ::
  ++  evaluate-constraints
    |=  $:  constraints=(list [(list @) mp-ultra])
            dyns=bpoly
            chal-map=(map @ belt)
            evals=fpoly
            chals=bpoly
        ==
    ^-  felt
    =-  acc
    %+  roll  constraints
    |=  [[degs=(list @) c=mp-ultra] [idx=@ acc=_(lift 0)]]
    ::
    ::  evaled is a list because the %comp constraint type
    ::  can contain multiple mp-mega constraints.
    =/  evaled=(list felt)  (mpeval-ultra %ext c evals chal-map dyns)
    %+  roll
      (zip-up degs evaled)
    |=  [[deg=@ eval=felt] [idx=_idx acc=_acc]]
    :-  +(idx)
    ::
    ::  Each constraint corresponds to two weights: alpha and beta. The verifier
    ::  samples 2*num_constraints random values and we assume that the alpha
    ::  and beta weights for a given constraint are situated next to each other
    ::  in the array.
    ::
    =/  alpha  (~(snag bop chals) (mul 2 idx))
    =/  beta   (~(snag bop chals) (add 1 (mul 2 idx)))
    ::
    ::  TODO: I've removed the degree adjustments but left it commented out. Once we figrue
    ::  out exactly how to do it we can put it back in.
    %+  fadd  acc
    %+  fmul  eval
    %+  fadd  (lift beta)
    %+  fmul  (lift alpha)
    (fpow deep-challenge (sub fri-deg-bound.dp deg))
  --  ::+eval-composition-poly
::
++  evaluate-deep
  ~/  %evaluate-deep
  |=  $:  trace-evaluations=fpoly
          comp-evaluations=fpoly
          trace-elems=(list belt)
          comp-elems=(list belt)
          num-comp-pieces=@
          weights=fpoly
          heights=(list @)
          full-widths=(list @)
          omega=felt
          index=@
          deep-challenge=felt
          new-comp-eval=felt
      ==
  ^-  felt
  =/  omega-pow  (fmul (lift g) (fpow omega index))
  |^
  =/  [acc=felt num=@ @]
    %^  zip-roll  (range (lent heights))  heights
    |=  [[i=@ height=@] acc=_(lift 0) num=@ total-full-width=@]
    =/  full-width  (snag i full-widths)
    =/  omicron  (lift (ordered-root height))
    =/  current-trace-elems  (swag [total-full-width full-width] trace-elems)
    =/  dat=[acc=felt num=@]  [acc num]
    ::  first row trace columns
    =/  denom  (fsub omega-pow deep-challenge)
    =.  dat
      %-  process-belt
      :*  current-trace-elems
          trace-evaluations
          weights
          full-width
          num.dat
          denom
          acc.dat
      ==
    ::  second row trace columns obtained by shifting by omicron
    =.  denom  (fsub omega-pow (fmul deep-challenge omicron))
    =.  dat
      %-  process-belt
      :*  current-trace-elems
          trace-evaluations
          weights
          full-width
          num.dat
          denom
          acc.dat
      ==
    [acc.dat num.dat (add total-full-width full-width)]
  ::
  ::
  =/  [acc=felt num=@ @]
    %^  zip-roll  (range (lent heights))  heights
    |=  [[i=@ height=@] acc=_acc num=_num total-full-width=@]
    =/  full-width  (snag i full-widths)
    =/  omicron  (lift (ordered-root height))
    =/  current-trace-elems  (swag [total-full-width full-width] trace-elems)
    =/  dat=[acc=felt num=@]  [acc num]
    ::  first row trace columns
    ::  evaluate new evals
    =/  denom  (fsub omega-pow new-comp-eval)
    =.  dat
      %-  process-belt
      :*  current-trace-elems
          trace-evaluations
          weights
          full-width
          num.dat
          denom
          acc.dat
      ==
    ::  second row trace columns obtained by shifting by omicron
    =.  denom  (fsub omega-pow (fmul new-comp-eval omicron))
    =.  dat
      %-  process-belt
      :*  current-trace-elems
          trace-evaluations
          weights
          full-width
          num.dat
          denom
          acc.dat
      ==
    [acc.dat num.dat (add total-full-width full-width)]
  ::
  =/  denom  (fsub omega-pow (fpow deep-challenge num-comp-pieces))
  =-  -<
  %-  process-belt
  :*  comp-elems
      comp-evaluations
      (~(slag fop weights) num)
      num-comp-pieces
      0
      denom
      acc
  ==
  ::
  ++  process-belt
    |=  $:  elems=(list belt)
            evals=fpoly
            weights=fpoly
            width=@
            num=@
            denom=felt
            acc=felt
        ==
    ^-  [felt @]
    %+  roll  (range width)
    |=  [i=@ acc=_acc num=_num]
    :_  +(num)
    %+  fadd  acc
    %+  fmul  (~(snag fop weights) num)
    %+  fdiv
      (fsub (lift (snag i elems)) (~(snag fop evals) num))
    denom
  --  ::+evaluate-deep
::
::  verify a list of merkle proofs in a random order. This is to guard against DDOS attacks.
++  verify-merk-proofs
  ~/  %verify-merk-proofs
  |=  [ps=(list merk-data:merkle) eny=@]
  ^-  ?
  =/  tog-eny  (new:tog:tip5 sponge:(absorb:(new:sponge:tip5) (mod eny p)^~))
  =/  lst=(list [@ merk-data:merkle])
    =-  l
    %+  roll  ps
    |=  [m=merk-data:merkle rng=_tog-eny l=(list [@ merk-data:merkle])]
    ^+  [tog:tip5 *(list [@ merk-data:merkle])]
    =^  rnd  rng  (belts:rng 1)
    :-  rng
    [[(head rnd) m] l]
  =/  sorted=(list [@ m=merk-data:merkle])
    %+  sort  lst
    |=  [x=[@ *] y=[@ *]]
    (lth -.x -.y)
  |-
  ?~  sorted  %.y
  =/  res  (verify-merk-proof:merkle m.i.sorted)
  ?.  res
    %.n
  $(sorted t.sorted)
--
