open util/relation

sig Tr {
    nxt: Op -> Op
} {
    functional[nxt, Op]
    injective[nxt, Op]
    irreflexive[nxt]
    antisymmetric[nxt]
    
    // starts with start operation
    some nxt[St]
    no nxt.St

    // ends with commit or abort operation
    some nxt.(Commit + Abort)
    no nxt[Commit + Abort]
}

abstract sig Op {
    tr: Tr
} {
    // Has to be in nxt
    this in dom[tr.nxt] + ran[tr.nxt]

    // Can't be in nxt of any other transaction
    this not in dom[(Tr-tr).nxt] + ran[(Tr-tr).nxt]
}

sig St,Commit,Abort extends Op {}

sig Obj {}

sig Val {}

abstract sig RW extends Op {
    obj: Obj,
    val: Val
}

sig Rd extends RW {}
sig Wr extends RW {}

run {some Op} for 4 but 1 Obj, 1 Val