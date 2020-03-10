datatype Edit<T> = Both(T) | Left(T) | Right(T)

function ApplyLeftStep<T>(edit: Edit<T>): seq<T>
{
    match edit
    case Both(c) => [c]
    case Left(c) => [c]
    case Right(_) => []
}

function ApplyLeft<T>(r: seq<Edit<T>>): seq<T>
    decreases r
{
    if r == []
    then []
    else ApplyLeftStep(r[0]) + ApplyLeft(r[1..])
}

// ghost method NaiveCorrectness<T>(s: seq<T>, t: seq<T>, r: seq<Edit<T>>)
//     // ensures Correctness(s, t, r);
//     requires r == Naive(s, t);
//     ensures ApplyLeft(r) == s;
// {
//     if s == [] {
//         // assert SeqMapEmpty(c => Left(c), s);
//         assert forall i :: 0 <= i < |r| ==> r[i].Right?;
//     } else {
//     }
// }



method Naive<T>(s: seq<T>, t: seq<T>)
    returns (r: seq<Edit<T>>)
    ensures |r| == |s| + |t|;
    ensures forall i :: 0 <= i < |s| ==> r[i].Left?;
    ensures forall i :: |s| <= i < |s| + |t| ==> r[i].Right?;
    // ensures ApplyLeft(r) == s;
{
    r := [];
    var rLen := 0;
    while rLen < |s|
        invariant |r| == rLen
        invariant 0 <= |r| <= |s|
        invariant forall k :: 0 <= k < rLen ==> r[k].Left?
        // invariant ApplyLeft(r[0..0]) == []
        // invariant s[0..0] == []
        // invariant ApplyLeft(r[0..0]) == s[0..0]
        decreases |s| - rLen
    {
        r := r + [Left(s[rLen])];
        rLen := rLen + 1;
    }
    // assert forall i :: 0 <= i < |s| ==> r[i].Left?;
    // assert rLen == |s|;

    while rLen < |s| + |t|
        invariant |r| == rLen
        invariant |s| <= rLen <= |s| + |t|
        invariant forall k :: 0 <= k < |s| ==> r[k].Left?
        invariant forall k :: |s| <= k < rLen ==> r[k].Right?
        decreases |s| + |t| - rLen
    {
        r := r + [Right(t[rLen - |s|])];
        rLen := rLen + 1;
    }
}
