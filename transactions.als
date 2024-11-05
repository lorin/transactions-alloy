open util/relation

sig Tr {
    nxt: Op -> Op,
    ops: disj set Op,
    vis: set Tr
} {
    // nxt is made up of ops
    nxt in ops -> ops

    // every op is in nxt
    all op : ops | some (op.nxt + nxt.op)

    functional[nxt, Op]
    injective[nxt, Op]
    irreflexive[nxt]
    antisymmetric[nxt]

    // starts with start operation
    one Start.nxt
    no nxt.Start

    // all ops are reachable from start
    ops in (Start & ops).*nxt

    // ends with commit or abort operation
    one nxt.(Commit + Abort)
    no (Commit + Abort).nxt
}

one sig T0 extends Tr {
} {
    ops in Start+Wr+Commit
    some nxt.Commit
    no vis

    all o : Obj | some w : Wr & ops { 
        w.obj = o 
        w.val = V0
    }
}

fact Visibility {
    // Can't have cyclic visibility
    acyclic[vis, Tr]

    // Transactions are not visible
    no Tr.vis & Abort.tr
}

abstract sig Op {
    tr: Tr
} {
    this in tr.ops
}

sig Start,Commit,Abort extends Op {}

sig Obj {}

sig Val {}

one sig V0 extends Val {}

abstract sig RW extends Op {
    obj: Obj,
    val: Val
}

sig Rd extends RW {
    sees: Wr
}
sig Wr extends RW {}

fact "write sees previous read in transaction" {
    all r : Rd | let w = r.sees  |
        // same transaction means there can't be an intervening write to the same object
        (r.tr = w.tr) => let t=r.tr, n=t.nxt, p=~n 
            | no w : w.n & r.^p | w.obj = r.obj
}


assert AbortsAreNotVisible {
    no Abort.tr & ran[vis]
}

run {some Op; some Wr; some Rd; some vis} for 11 but 1 Obj, 1 Val

// check AbortsAreNotVisible for 4 but 1 Obj, 1 Val 
