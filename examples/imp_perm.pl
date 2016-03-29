[imp(p,imp(q,r))].

imp(q,imp(p,r)).

[
  [1, imp(p,imp(q,r)), premise],
  [
    [2, q, assumption],
    [
      [3, p, assumption],
      [4, imp(q,r), impel(3,1)],
      [5, r, impel(2, 4)]
    ],
    [6, imp(p, r), impint(3,5)]
  ],
  [7, imp(q,imp(p,r)), impint(2,6)]
].
