/*

Source: Generalized Isolation Level Definitions,
Atul Adya, Barbara Liskov, Patrick O'Neil.
Proceedings of the IEEE International Conference on Data Engineering, March 2000.

https://pmg.csail.mit.edu/papers/icde00.pdf

*/

open util/ordering[Version] as vo
open util/ordering[Op] as oo

// transactions
abstract sig Tr {
    ops : set Op
}

// committed transactions
sig TrC extends Tr {}

// aborted transactions
sig TrA extends Tr {}

// Operations
abstract sig Op {
    tr: Tr,
    tn: lone Op // transaction-next (next op in transaction)
} {
    this in tr.ops // this op is in the operations of the transactions it is associated with
    one ~ops[this] // this op is associated with exactly one transaction
}


// read-write operations
abstract sig RWOp extends Op {
    obj: Obj,
    val: Val
}

// writes
sig Wr extends RWOp {}

// reads
sig Rd extends RWOp {
    sees: Wr
} {
    obj = sees.@obj
    val = sees.@val
}

run {no PRead; some Rd} for 3 but exactly 10 Op, exactly 2 Obj, exactly 3 Val


//  Predicate read
sig PRead extends Op {
    vset: some VersionedValue,
    objs : set Obj,
    P: Predicate,
} {
    // sees a write for every object
    Obj in vset.w.obj

    // vset contains a version of every object
    Obj in vset.obj

    // matching set of objects consistent with predicate evaluation
    objs = P.eval[wr_env[vset.w]]

    // predicates see only one write per object
    no disj w1, w2 : vset.w | w1.obj = w2.obj
}
 

sig Predicate {
    eval: Env -> set Obj
}



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

pred G1 {
    G1a or G1b or G1c
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


fun DSG[] : TrC -> TrC {
    ww + wr + rw
}

/*
G2: Anti-dependency Cycles. A history H exhibits
phenomenon G2 if DSG(H) contains a directed cycle
with one or more anti-dependency edges.
*/
pred G2 {
    // must contain a cycle
    some iden & ^DSG

    // must not contain a cycle if there are no antidependency edges
    no iden & ^(DSG - rw)
}


/*
G2-item: Item Anti-dependency Cycles. A history H exhibits phenomenon G2-item if
DSG(H) contains a directed cycle having one or more item-antidependency edges.
*/
pred G2item {
    // must contain a cycle
    some iden & ^DSG

    // must not contain a cycle if there are no item-antidependency edges
    no iden & ^(DSG - irw)
}

/*
we define PL-1 as the level in which
G0 is disallowed
*/
assert PL1 {
    not G0
}


assert PL2 {
    not G0
    not G1
}

assert PL2_99 {
    not G0
    not G1
    not G2item
}

assert PL3 {
    not G0
    not G1
    not G2
}


/*
Definition 3: Directly Read-Depends.

We say that Tj directly read-depends on transaction Ti if it directly
item-read-depends or directly predicate-read-depends on Ti
*/
fun wr[] : TrC -> TrC {
    iwr + pwr
}

/*
Directly item-read-depends:

We say that Tj directly itemread-depends on Ti if Ti installs some object version
xi and Tj reads xi
*/
fun iwr[] : TrC -> TrC {
    { Ti: TrC, Tj: TrC  | some o : Obj, vv : o.vers, rd : Rd & Tj.ops | {
        vv.tr = Ti
        rd.obj = o
        rd.sees.tr = Ti
    }} - iden
}

pred changes_the_matches_of[xi : VersionedValue, pr : PRead] {
    // xi is the versioned value that corresponds to a write
    let xp = {xp : VersionedValue | xp.obj = xi.obj and xp.v = prev[xi.v]},
        wrs = (pr.vset.w - xi.w) + xp.w,
        env_prev = wr_env[wrs],
        P = pr.P |

        pr.objs != P.eval[env_prev]
}

/*
Directly predicate-read-depends: Transaction Tj directly
predicate-read-depends on Ti if Tj performs an operation rj (P: Vset(P)),
xk ∈ Vset(P), i = k or xi << xk, and xi changes the matches of rj (P: Vset(P)).
*/
fun pwr[] : TrC -> TrC {
    {Ti : TrC, Tj: TrC | some rj : PRead & Tj.ops, xk : rj.vset |
        some xi : xk.obj.vers | {
            xi.tr = Ti
            (xi = xk) or {
                lt[xi.v, xk.v]
                // xi changes the matches of rj (P: Vset(P))
                changes_the_matches_of[xi, rj]
            }
        }
    } - iden
}

assert NoPredicateWriteDeps {
    no pwr
}

check NoPredicateWriteDeps


/*
Definition 5 : Directly Anti-Depends.

Transaction Tj directly anti-depends on transaction Ti if it directly
item-anti-depends or directly predicate-anti-depends on T i
*/
fun rw[] : TrC->TrC {
    irw + prw
}

/*
Directly item-anti-depends: We say that Tj directly item-anti-depends on
transaction Ti if Ti reads some object version xk and Tj installs x’s next
version (after xk ) in the version order. Note that the transaction that wrote
the later version directly item-anti-depends on the transaction that read the
earlier version
*/
fun irw[] : TrC -> TrC {
    {Ti: TrC, Tj: TrC | some rd : Rd & Ti.ops, xk : rd.obj.vers | {
        rd.val = xk.val
        nextv[xk].tr = Tj
        no xk.val & nextv[xk].val // enforce different values being written
    }} - iden
}

fun nextv[vv : VersionedValue] : lone VersionedValue {
    { w : VersionedValue | {
        vv.obj = w.obj
        w.v = next[vv.v] }}
}


/*
Directly predicate-anti-depends: We say that Tj directly
predicate-anti-depends on Ti if Tj overwrites an operation ri (P: Vset(P)),
 i.e., Tj installs a later version of some object that changes 
 the matches of a predicate based read performed by Ti
*/
fun prw[] : TrC->TrC {
    {Ti: TrC, Tj: TrC | 
        some ri : PRead & Tj.ops, vv : VersionedValue {
            vv.tr = Tj
            changes_the_matches_of[vv, ri]
        }
    }
}

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
        no vv1.val & vv2.val // enforce different values being written
        next[vv1.v] = vv2.v }} - iden
}

sig Env {
    mapping : Obj -> one Val
} {
    // env contains every object
    Obj in mapping.Val
}

/**
 * Given a set of object writes, return the correspond Env
 * that maps objects to their written values
 */
fun wr_env[wrs : set Wr] : Env {
    {e : Env | all o : Obj | e.mapping[o] = written[o, wrs]}
}

fun written[o: Obj, wrs: set Wr] : Val {
    {wr : wrs | wr.obj = o}.val
}

fact TransactionNext {
    tn = { disj o1, o2 : Op | {
            o1.tr = o2.tr
            o1->o2 in ^oo/next
            no o3 : Op | {
                o3.tr = o1.tr 
                o1->o3 in ^oo/next 
                o3->o2 in ^oo/next
            }
        } }
}


// Objects
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
    tr : TrC,
    w : Wr
} {
    this in obj.vers

    // For every installed VersionedValue, there must be an associated write in the transaction
    w in tr.ops
    w.@obj = obj
    w.@val = val
}

// values
sig Val {}

// versions
sig Version {}



// check PL1
// check PL2 for 3 but exactly 1 Obj

// check PL3 for 4


run {some Predicate} for 3 but exactly 2 Tr, exactly 5 Op


/*
run {
    all t : Tr | some tr.t
    all obj : Obj | #obj.vers > 1

} for 3 but exactly 3 Tr, exactly 2 Obj, exactly 3 Version
*/