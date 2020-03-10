datatype Edit<T> = Both(T) | Left(T) | Right(T)

datatype Option<T> = Some(T) | None

// predicate Correctness(s: string, t: string, edits: seq<Edit>)
// {
//    ApplyLeft(edits) == s && ApplyRight(edits) == t
// }


function SeqMap<T, U>(f: T -> U, l: seq<T>): seq<U>
    decreases l;
{
    if l == []
    then []
    else [f(l[0])] + SeqMap(f, l[1..])
}

ghost method SeqMapEmpty<T, U>(f: T -> U, l: seq<T>)
    requires l == [];
    ensures SeqMap(f, l) == [];
{}

function SeqCatOptions<T>(l: seq<Option<T>>): seq<T>
    decreases l;
{
    if l == []
    then []
    else (
        match l[0]
        case Some(v) => [v] + SeqCatOptions(l[1..])
        case None => SeqCatOptions(l[1..])
    )
}

function ApplyLeftStep<T>(edit: Edit<T>): Option<T>
{
    match edit
    case Both(c) => Some(c)
    case Left(c) => Some(c)
    case Right(_) => None
}

function ApplyLeft<T>(edits: seq<Edit<T>>): seq<T>
    decreases edits;
{
    SeqCatOptions(SeqMap(ApplyLeftStep, edits))
    // if edits == []
    // then []
    // else ((
    //     match edits[0]
    //     case Both(c) => c
    //     case Left(c) => c
    //     case Right(_) => []
    // ) + ApplyLeft(edits[1..]))
}

// function ApplyRight(edits: seq<Edit>): string
//     decreases edits;
// {
//     if edits == []
//     then []
//     else ((
//         match edits[0]
//         case Both(s) => s
//         case Left(_) => []
//         case Right(s) => s
//     ) + ApplyRight(edits[1..]))
// }

ghost method NaiveCorrectness<T>(s: seq<T>, t: seq<T>, edits: seq<Edit<T>>)
    // ensures Correctness(s, t, edits);
    requires edits == Naive(s, t);
    ensures ApplyLeft(edits) == s;
{
    if s == [] {
        // assert SeqMapEmpty(c => Left(c), s);
        assert forall i :: 0 <= i < |edits| ==> edits[i].Right?;
    } else {
    }
}

function Naive<T>(s: seq<T>, t: seq<T>): seq<Edit<T>>
{
    SeqMap(c => Left(c), s) + SeqMap(c => Right(c), t)
}

ghost method NaiveNoOverlap<T>(s: seq<T>, t: seq<T>, edits: seq<Edit<T>>)
    requires edits == Naive(s, t);
    ensures forall i :: 0 <= i < |edits| ==> (edits[i].Left? || edits[i].Right?);
{
    if edits == [] {}
    else {

    }
}


// method Naive(s: string, t: string)
//     returns (edits: seq<Edit>)
//     ensures ApplyLeft(edits) == s;
//     ensures ApplyRight(edits) == t;
//     ensures Correctness(s, t, edits);
// {
//     return [Left(s), Right(t)];
// }
