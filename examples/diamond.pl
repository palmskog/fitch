[].

imp(imp(p,q),imp(imp(p,r),imp(imp(q,imp(r,s)),imp(p,s)))).

[
  [
    [1, imp(p,q), assumption],
    [
      [2, imp(p,r), assumption],
      [
        [3, imp(q,imp(r,s)), assumption],
        [
	  [4, p, assumption],
	  [5, q, impel(4,1)],
	  [6, r, impel(4,2)],
	  [7, imp(r,s), impel(5,3)],
	  [8, s, impel(6,7)]
        ],
        [9, imp(p,s), impint(4,8)]
      ],
      [10, imp(imp(q,imp(r,s)),imp(p,s)), impint(3,9)]
    ],
    [11, imp(imp(p,r),imp(imp(q,imp(r,s)),imp(p,s))), impint(2, 10)]
  ],
  [12, imp(imp(p,q),imp(imp(p,r),imp(imp(q,imp(r,s)),imp(p,s)))), impint(1, 11)]
].

