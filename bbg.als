/**
 * Based on the following paper:
 *
 * A Critique of ANSI SQL Isolation Levels
 *
 * Hal Berenson, Phil Bernstein, Jim Gray, Jim Melton, Elizabeth O'Neil, Patrick O'Neil,
 * Microsoft Research Technical Report MSR-TR-95-51, June 1995.
 * https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-95-51.pdf
 */


open transactions as t
open util/ordering[Event] as geo

let gnext = geo/next
let teo = *gnext

// check { AnsiReadCommittedStrict } for 4

/**
 * Table 1
 */
pred AnsiReadCommittedBroad {
    not P1
}


pred AnsiReadCommittedStrict {
    not A1
}

pred AnsiRepeatableReadBroad {
    not P1
    not P2
}

pred AnsiRepeatableReadStrict {
    not A1
    not A2
}

pred AnomalySerializableBroad {
    not P1
    not P2
    not P3
}

pred AnomalySerializableStrict {
    not A1
    not A2
    not A3
}


pred adjacent[n1 : univ, n2 : univ, r: univ->univ, s : set univ] {
    n1->n2 in r
    no n3 : s - (n1+n2)  | {
        n1->n3 in r
        n3->n2 in r
    }
}

fun gnext[] : Event -> Event  {
    {disj e1, e2 : Event | e1->e2 in teo }
}

fact "gnext is consistent with eo" {
    eo in teo
}


fact "cannot see writes from the future" {
    ~sees in ^gnext
}


/**
* P1: w1[x]...r2[x]...((c1 or a1) and (c2 or a2) in any order)
*/
pred P1 {
    some disj T1, T2 : Transaction,
              w1 : Write & events[T1],
              r2 : Read & events[T2],
              c1_or_a1 : T1.events & (Commit + Abort) | {
        w1->r2 in teo
        r2.sees = w1
        // r2 has to happen before T1 completes
        r2->c1_or_a1 in teo
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

       w1->r2 in teo
       r2.sees = w1
       // r2 has to happen before T1 aborts
       r2->a1 in teo
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

        r1->w2 in teo
        w2->c1_or_a1 in teo
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
        r1->w2 in teo
        w2->c2 in teo
        c2->r1 in teo
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
                r1->w2 in teo
                w2->c1_or_a1 in teo
                w2.obj in r1.objs
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
                r1a->w2 in teo
                w2->c2 in teo
                c2->r1b in teo
                w2.obj in r1a.objs
                }
  }