//
//
// Phenomena from BBG+
//
//

open transactions


check { A3 <=> P3 } for 5


pred adjacent[n1 : univ, n2 : univ, r: univ->univ, s : set univ] {
    n1->n2 in r
    no n3 : s - (n1+n2)  | {
        n1->n3 in r
        n3->n2 in r
    }
}

fun gnext[] : Event -> Event  {
    {disj e1, e2 : Event | adjacent[e1, e2, eo, Event] }
}


/**
* P1: w1[x]...r2[x]...((c1 or a1) and (c2 or a2) in any order)
*/
pred P1 {
    some disj T1, T2 : Transaction,
              w1 : Write & events[T1],
              r2 : Read & events[T2],
              c1_or_a1 : T1.events & (Commit + Abort) | {
        w1->r2 in eo
        r2.sees = w1
        // r2 has to happen before T1 completes
        r2->c1_or_a1 in eo
    }
}

/**
 * A1: w1[x]...r2[x]...(a1 and c2 in any order)
 */
pred A1 {
    some T1 : AbortedTransaction,
         T2 : CommittedTransaction,
         w1: Write & events[T1],
         r2 : Read & events[T2],
         a1 : Abort & events[T1] | {

       w1->r2 in eo
       r2.sees = w1
       // r2 has to happen before T1 aborts
       r2->a1 in eo
    }
}

/**
 * P2: r1[x]...w2[x]...((c1 or a1) and (c2 or a2) in any order)
 */
 pred P2 {
    some disj T1, T2 : Transaction,
              r1 : Read & events[T2],
              w2 : Write & events[T1],
              c1_or_a1 : T1.events & (Commit + Abort) | {

        r1->w2 in eo
        w2->c1_or_a1 in eo
    }
 }

/**
 * A2: r1[x]...w2[x]...c2...r1[x]...c1
 */
 pred A2 {
    some disj T1, T2 : CommittedTransaction,
              r1 : Read & events[T1],
              w2 : Write & events[T2],
              c2 : Commit & events[T2]
               | {
        r1->w2 in eo
        w2->c2 in eo
        c2->r1 in eo
        r1.sees = w2
    }
 }

 /**
  * P3: r1[P]...w2[y in P]...((c1 or a1) and (c2 or a2) any order)
  */
  pred P3 {
    some disj T1, T2 : Transaction,
              r1 : PredicateRead & events[T1],
              w2 : Write & events[T2],
              c1_or_a1 : (Abort + Commit) & events[T1] | {
                r1->w2 in eo
                w2->c1_or_a1 in eo
                w2.obj in r1.vset.vs.obj
              }
  }

/**
 * A3: r1[P]...w2[y in P]...c2...r1[P]...c1
 */
 pred A3 {
    some disj T1, T2 : CommittedTransaction,
              r1a, r1b : PredicateRead & events[T1],
              w2 : Write & events[T2],
              c2 : Commit & events[T2] | {
                r1a.p = r1b.p
                r1a->w2 in eo
                w2->c2 in eo
                c2->r1b in eo
                w2.obj in r1a.vset.vs.obj
                }
  }