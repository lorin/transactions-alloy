sig Tr {
    nxt: Op -> Op
}

abstract sig Op {
    tr: Tr
}

sig St,Rd,Wr,Co,Ab extends Op {}


run {some Op}