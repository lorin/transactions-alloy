open util/relation
open util/ordering[Version]

abstract sig Tr {
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
}

sig CTr extends Tr {} {
    // ends with commit 
    one nxt.Commit
    no Commit.nxt

    // no abort
    no Abort & ops
}

sig ATr extends Tr {} {
    // ends with abort operation
    one nxt.Abort
    no Abort.nxt

    // no commit
    no Commit & ops
}



one sig T0 extends CTr {
} {
    ops in Start+Wr+Commit
    no vis

    // every object has a write of V0
    all o : Obj | some w : Wr & ops { 
        w.obj = o 
        w.val = V0
    }

    // Only one write per object
    no disj o1, o2 : Wr & ops | o1.obj = o2.obj

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

sig Start, Commit, Abort extends Op {}

sig Obj {
    ver : set VersionedValue
} {
    // versions are all unique
    no disj v1, v2 : ver | v1.v = v2.v
}

sig VersionedValue {
    v : Version,
    val : Val,
    tr : Tr
}

fact "all committed writes install a value" {
    all t : Tr |
        (some t.ops & Commit) => 
            all w : Wr & t.ops | w.obj.ver.tr = t
}

fact "versions are installed sequentially" {
    all o : Obj, v1 : o.ver |
        (v1.v != ordering/first) => some v2 : o.ver | ordering/lt[v2.v, v1.v]
}


sig Val {}

one sig V0 extends Val {}

sig Version {}

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


/* Write dependencies between transactions */
fun ww[] : Tr -> Tr {
    Tr -> Tr
}


assert AbortsAreNotVisible {
    no Abort.tr & ran[vis]
}

run {some Op; some Wr; some Rd; some vis} for 11 but 1 Obj, 1 Val

// check AbortsAreNotVisible for 4 but 1 Obj, 1 Val 
