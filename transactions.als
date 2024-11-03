open util/relation

sig Tr {
    nxt: Op -> Op
} {
    irreflexive[nxt]
    antisymmetric[nxt]
    injective[nxt, Op]
}

abstract sig Op {
    tr: Tr
}

sig St,Rd,Wr,Co,Ab extends Op {}


run {some Op}