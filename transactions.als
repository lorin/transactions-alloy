open util/relation

sig Tr {
    nxt: Op -> Op,
    ops: set Op,
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
    some nxt[Start]
    no nxt.Start

    // ends with commit or abort operation
    some nxt.(Commit + Abort)
    no nxt[Commit + Abort]

    // all ops are reachable from start
    ops in (Start & ops).*nxt
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

fact WritesSeePreviousReadinTransaction {
    all r : Rd | 
    let next = r.tr.nxt, prev = ~next |
        (some w : (^prev).r & Wr | {
            r.obj=w.obj
            no ww : w.^next & (^prev).r | r.obj=ww.obj
        })
}

assert AbortsAreNotVisible {
    no Abort.tr & ran[vis]
}

run {some Op; some Wr; some Rd; some vis} for 4 but 1 Obj, 1 Val

/* check AbortsAreNotVisible for 4 but 1 Obj, 1 Val */
