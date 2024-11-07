/*

Source: Generalized Isolation Level Definitions,
Atul Adya, Barbara Liskov, Patrick O'Neil. 
Proceedings of the IEEE International Conference on Data Engineering, March 2000.

https://pmg.csail.mit.edu/papers/icde00.pdf

*/


open util/ordering[Version] as vo
open util/ordering[Op] as oo

fun vn[] : Version -> Version {
    vo/next
}

/*
G0: Write Cycles. A history H exhibits phenomenon
G0 if DSG(H) contains a directed cycle consisting
entirely of write-dependency edges.
*/
pred G0 {
    some iden & ^ww[]
}

/*
G1a: Aborted Reads

A history H shows phenomenon G1a if it contains an aborted transaction T1 and a
committed transaction T2 such that T2 has read some object modified by T1

*/
pred G1a {
    some T1 : TrA, T2 : TrC, r : T2.ops & Rd, w : T1.ops & Wr | r.sees = w
}

/* 
G1b: Intermediate Reads. A history H shows phenomenon G1b if it contains a committed transaction
T2 that has read a version of object x written by transaction T1 that was not T1’s
final modification of x.
*/
pred G1b {
    some disj T1, T2 : TrC, r : T2.ops & Rd | let x = r.obj, wi=r.sees | 
    {
        wi.tr = T1
        some wj : (T1.ops - wi) & Wr | {
            wj.obj = x
            gt[wj, wi]
        }
    }
}


/*
G1c: Circular Information Flow. 

A history H exhibits phenomenon G1c if DSG(H) contains a directed cycle
consisting entirely of dependency edges
*/
pred G1c {
    some iden & ^(ww + wr)
}

/*
G2-item: Item Anti-dependency Cycles. A history H exhibits phenomenon G2-item if
DSG(H) contains a directed cycle having one or more item-antidependency edges.
*/

fun DSG[] : TrC -> TrC {
    ww + wr + rw
}

pred G2item {
    some iden & ^DSG
    not G1c
}

/*
we define PL-1 as the level in which
G0 is disallowed
*/
assert PL1 {
    not G0
}


assert PL2 {
    not G1a
    not G1b
    not G1c
}

assert PL3 {
    not G2item
}

abstract sig Tr {
    ops : set Op
}

// committed transactions
sig TrC extends Tr {}

// aborted transactions
sig TrA extends Tr {}


abstract sig Op {
    tr: Tr,
    obj: Obj,
    val: Val,
    tn: lone Op // transaction-next (next op in transaction)
} {
    this in tr.ops // this op is in the operations of the transactions it is associated with
    one ~ops[this] // this op is associated with exactly one transaction
}

fact TransactionNext {
    tn = { disj o1, o2 : Op | {
            o1.tr = o2.tr 
            o1->o2 in ^oo/next 
            no o3 : Op | o1->o3 in ^oo/next and o3->o2 in ^oo/next
        } }
}

sig Wr extends Op {}

sig Rd extends Op {
    sees: Wr
} {
    obj = sees.@obj
    val = sees.@val
}


sig Obj {
    vers : set VersionedValue
} {
    this in vers.obj

    // each version val is associated with a unique transaction
    no disj vv1, vv2 : vers | {
        vv1.tr = vv2.tr
    }

    // only one of each version
    no disj vv1, vv2 : vers | {
        vv1.v = vv2.v 
    }
}

sig VersionedValue {
    obj: Obj,
    v : Version,
    val : Val,
    tr : TrC
} 

sig Val {}

sig Version {}

/*
Definition 6 : Directly Write-Depends. 

A transaction Tj
directly write-depends on Ti if Ti installs a version xi and
Tj installs x’s next version (after xi ) in the version order

Ti -> Tj

*/
fun ww[] : TrC -> TrC {
    { Ti: TrC, Tj: TrC  | some obj : Obj, vv1,vv2 : obj.vers | {
        vv1.tr = Ti
        vv2.tr = Tj
        next[vv1.v] = vv2.v }}
}

/*
Direction 3: Directly Read-Depends.

We say that Tj directly read-depends on transaction Ti if it directly
itemread-depends or directly predicate-read-depends on T i 

Directly item-read-depends: 

We say that Tj directly itemread-depends on Ti if Ti installs some object version
xi and Tj reads xi 
*/
fun wr[] : TrC -> TrC {
    { Ti: TrC, Tj: TrC  | some o : Obj, vv : o.vers, rd : Rd & Tj.ops | {
        vv.tr = Ti
        rd.obj = o
        rd.sees.tr = Ti
    }} - iden
}

fun nextv[vv : VersionedValue] : VersionedValue {
    { w : VersionedValue | {
        vv.obj = w.obj
        w.v = next[vv.v] }}
}


/*
Definition 5 : Directly Anti-Depends. 

Transaction Tj directly anti-depends on transaction Ti if it directly
item-anti-depends or directly predicate-anti-depends on T i

Directly item-anti-depends: We say that Tj directly item-anti-depends on
transaction Ti if Ti reads some object version xk and Tj installs x’s next
version (after xk ) in the version order. Note that the transaction that wrote
the later version directly item-anti-depends on the transaction that read the
earlier version
*/
fun rw[] : TrC -> TrC {
    {Ti: TrC, Tj: TrC | some rd : Rd & Ti.ops, xk : rd.obj.vers | nextv[xk].tr = Tj } 
}


// check PL1 
// check PL2 for 3 but exactly 1 Obj

check PL3


// run {} for 3 but exactly 2 Tr, exactly 5 Op


/*
run {
    all t : Tr | some tr.t
    all obj : Obj | #obj.vers > 1

} for 3 but exactly 3 Tr, exactly 2 Obj, exactly 3 Version
*/