open util/relation

sig Tr {
    nxt: Op -> Op
} {
    irreflexive[nxt]
    antisymmetric[nxt]
    injective[nxt, Op]
    some nxt[St]
    no ~nxt[St]
    // some nxt[Co + Ab]
}

abstract sig Op {
    tr: Tr
}

sig St,Rd,Wr,Co,Ab extends Op {}


run {some Op}