[].

imp(imp(imp(imp(imp(p,q),p),p),q),q).

[
  [
    [1, imp(imp(imp(imp(p,q),p),p),q), assumption],
    [
     [2, imp(imp(p,q),p), assumption],
     [
       [3, p, assumption],
       [
        [4, imp(imp(p,q),p), assumption],
        [5, p, copy(3)]
       ],
       [6, imp(imp(imp(p,q),p),p), impint(4,5)],
       [7, q, impel(6,1)]
     ],
     [8, imp(p,q), impint(3,7)],
     [9, p, impel(8,2)]
   ],
   [10, imp(imp(imp(p,q),p),p), impint(2,9)],
   [11, q, impel(10,1)]
  ],
  [12, imp(imp(imp(imp(imp(p,q),p),p),q),q), impint(1,11)]
].
