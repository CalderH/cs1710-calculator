#lang forge

option problem_type temporal
option max_tracelength 10

one sig DoneFlag {}

sig Thread {
    var tstack: set Int -> Int, // index -> value, bottom of the stack is index 0
    var pc: one Int, // PC is program counter
    var done: lone DoneFlag
} 

abstract sig Operation {}
one sig Addition, Multiplication, Subtraction, Division, Remainder, Bring, Send, Copy, Remove, Swap, Drop, Equal, Greater, Less, GreaterEqual, LessEqual, If, Jump extends Operation {}
sig Push extends Operation {
    num: one Int
}
one sig END extends Operation {}

// Nothing is var here; nothing changes
one sig OperationList {
	list : set Int -> Operation  // index -> Operation, first operation is index 0
}

// TODO: what about bit overflow
pred stackIndicesInOrder[thread : Thread]{
    one (sing[0]).(thread.tstack) // Must have 0
    one i : (thread.tstack).Int | { // Everything but the top has a successor
        no (i.succ).(thread.tstack)
    }
    all i : (thread.tstack).univ | {sum[i] >= 0}
    // no sing[-1].(thread.tstack) // No negatives
    ~(thread.tstack).(thread.tstack) in iden // One value for every index
}

pred operationIndicesInOrder{
    one (sing[0]).(OperationList.list)
    one i : (OperationList.list).Operation | {
        no (i.succ).(OperationList.list)
    }
    all i : (OperationList.list).univ | {sum[i] >= 0}
    // no sing[-1].(OperationList.list)
    ~(OperationList.list).(OperationList.list) in iden
}


pred init {
    Thread.pc = sing[0]
    some list
    some list.END
    (OperationList.list)[sing[0]] != END
    // #list > 0 // no overflow
    no done
    // all t : Thread | some t.tstack
    all t : Thread | stackIndicesInOrder[t]
    operationIndicesInOrder
}


----------------------------------------

fun getTopFrameIndex[thread : Thread] : one Int {
    sing[max[thread.tstack.Int]]
}

fun getTopFrameValue[thread : Thread] : one Int {
    thread.tstack[getTopFrameIndex[thread]]
}

fun getSecondToTopFrameValue[thread : Thread] : one Int {
    thread.tstack[succ.(getTopFrameIndex[thread])]
}

fun getThirdToTopFrameValue[thread : Thread] : one Int {
    thread.tstack[succ.succ.(getTopFrameIndex[thread])]
}

//TODO: How can we make a popn?

fun pop1[thread : Thread] : set Int -> Int {
    thread.tstack - (getTopFrameIndex[thread] -> Int)
}

fun pop2[thread : Thread] : set Int -> Int {
    thread.tstack - (getTopFrameIndex[thread] -> Int) - (succ.(getTopFrameIndex[thread]) -> Int)
}

fun pop3[thread : Thread] : set Int -> Int {
    thread.tstack - (getTopFrameIndex[thread] -> Int) - (succ.(getTopFrameIndex[thread]) -> Int) - (succ.succ.(getTopFrameIndex[thread]) -> Int)
}

pred addStuff[t : Thread] {
    (t.pc).(OperationList.list) = Addition
    sum[getTopFrameIndex[t]] > 0 --you have enough frames (ie more than 1)

    t.pc' = (t.pc).succ --point to the next place in the program counter
    t.tstack' = pop2[t] + (succ.(getTopFrameIndex[t]) -> sing[add[sum[getSecondToTopFrameValue[t]], sum[getTopFrameValue[t]]]])
}

pred subtractStuff[t : Thread] {
    (t.pc).(OperationList.list) = Subtraction
    sum[getTopFrameIndex[t]] > 0 --you have enough frames (ie more than 1)

    t.pc' = (t.pc).succ --point to the next place in the program counter
    t.tstack' = pop2[t] + (succ.(getTopFrameIndex[t]) -> sing[subtract[sum[getSecondToTopFrameValue[t]], sum[getTopFrameValue[t]]]])
}

pred multiplyStuff[t : Thread] {
    (t.pc).(OperationList.list) = Multiplication
    sum[getTopFrameIndex[t]] > 0 --you have enough frames (ie more than 1)

    t.pc' = (t.pc).succ --point to the next place in the program counter
    t.tstack' = pop2[t] + (succ.(getTopFrameIndex[t]) -> sing[multiply[sum[getSecondToTopFrameValue[t]], sum[getTopFrameValue[t]]]])
}

pred divideStuff[t : Thread] {
    (t.pc).(OperationList.list) = Division
    getTopFrameValue[t] != sing[0]
    sum[getTopFrameIndex[t]] > 0 --you have enough frames (ie more than 1)

    t.pc' = (t.pc).succ --point to the next place in the program counter
    t.tstack' = pop2[t] + (succ.(getTopFrameIndex[t]) -> sing[divide[sum[getSecondToTopFrameValue[t]], sum[getTopFrameValue[t]]]])
}

pred remainderStuff[t : Thread] {
    (t.pc).(OperationList.list) = Remainder
    getTopFrameValue[t] != sing[0]
    sum[getTopFrameIndex[t]] > 0 --you have enough frames (ie more than 1)

    t.pc' = (t.pc).succ --point to the next place in the program counter
    t.tstack' = pop2[t] + (succ.(getTopFrameIndex[t]) -> sing[remainder[sum[getSecondToTopFrameValue[t]], sum[getTopFrameValue[t]]]])
}

pred bringStuff[t: Thread] {
    (t.pc).(OperationList.list) = Bring
    sum[getTopFrameValue[t]] >= 0
    sum[getTopFrameValue[t]] <= subtract[#t.tstack, 2]
    
    t.pc' = (t.pc).succ
    all i : Int {
        -- Stack elements before the one that was brought to the front
        (sum[i] <= subtract[#t.tstack, sum[getTopFrameValue[t]], 3]) => (
            (t.tstack')[i] = (t.tstack)[i]
        )
        -- Elements after the one that was brought to the front
        (sum[i] > subtract[#t.tstack, sum[getTopFrameValue[t]], 3] && sum[i] <= subtract[#t.tstack, 3]) => (
            (t.tstack')[i] = (t.tstack)[i.succ]
        )
        -- The new front element
        (sum[i] = subtract[#t.tstack, 2]) => (
            (t.tstack')[i] = (t.tstack)[sing[subtract[#t.tstack, sum[getTopFrameValue[t]], 2]]]
        )
        -- Nothing after that
        (sum[i] > subtract[#t.tstack, 2]) => (
            no (t.tstack')[i]
        )
    }
}

pred sendStuff[t: Thread] {
    (t.pc).(OperationList.list) = Send
    sum[getTopFrameValue[t]] >= 0
    sum[getTopFrameValue[t]] <= subtract[#t.tstack, 2]

    t.pc' = (t.pc).succ
    all i : Int {
        -- Stack elements before the sent element
        (sum[i] <= subtract[#t.tstack, sum[getTopFrameValue[t]], 3]) => (
            (t.tstack')[i] = (t.tstack)[i]
        )
        -- The sent element
        (sum[i] = subtract[#t.tstack, sum[getTopFrameValue[t]], 2]) => (
            (t.tstack')[i] = getSecondToTopFrameValue[t]
        )
        -- Elements after the sent element
        (sum[i] > subtract[#t.tstack, sum[getTopFrameValue[t]], 2] && sum[i] <= subtract[#t.tstack, 2]) => (
            (t.tstack')[i] = (t.tstack)[succ.i]
        )
        -- Nothing after that
        (sum[i] > subtract[#t.tstack, 2]) => (
            no (t.tstack')[i]
        )
    }
}

pred copyStuff[t: Thread] {
    (t.pc).(OperationList.list) = Copy
    sum[getTopFrameValue[t]] >= 0
    sum[getTopFrameValue[t]] <= subtract[#t.tstack, 2]

    t.pc' = (t.pc).succ
    t.tstack' = pop1[t] + getTopFrameIndex[t]->((t.tstack)[sing[subtract[#t.tstack, sum[getTopFrameValue[t]], 2]]])
}

pred removeStuff[t: Thread] {
    (t.pc).(OperationList.list) = Remove
    sum[getTopFrameValue[t]] >= 0
    sum[getTopFrameValue[t]] <= subtract[#t.tstack, 2]

    t.pc' = (t.pc).succ
    all i : Int {
        -- Stack elements before the one that was removed
        (sum[i] <= subtract[#t.tstack, sum[getTopFrameValue[t]], 3]) => (
            (t.tstack')[i] = (t.tstack)[i]
        )
        -- Elements after the one that was removed
        (sum[i] > subtract[#t.tstack, sum[getTopFrameValue[t]], 3] && sum[i] <= subtract[#t.tstack, 3]) => (
            (t.tstack')[i] = (t.tstack)[i.succ]
        )
        -- Nothing after that
        (sum[i] > subtract[#t.tstack, 3]) => (
            no (t.tstack')[i]
        )
    }
}

pred swapStuff[t: Thread] {
    (t.pc).(OperationList.list) = Swap
    sum[getTopFrameIndex[t]] > 0

    t.pc' = (t.pc).succ
    t.tstack' = pop2[t] + (succ.(getTopFrameIndex[t]) -> getTopFrameValue[t]) + (getTopFrameIndex[t] -> getSecondToTopFrameValue[t])
}

pred dropStuff[t: Thread] {
    (t.pc).(OperationList.list) = Drop
    some t.tstack

    t.pc' = (t.pc).succ
    t.tstack' = pop1[t]
}

pred equalStuff[t : Thread] {
    (t.pc).(OperationList.list) = Equal
    sum[getTopFrameIndex[t]] > 0 --you have enough frames (ie more than 1)

    t.pc' = (t.pc).succ --point to the next place in the program counter
    (getSecondToTopFrameValue[t] = getTopFrameValue[t]) => (t.tstack' = t.tstack + (getTopFrameIndex[t].succ)->sing[1])
    (not getSecondToTopFrameValue[t] = getTopFrameValue[t]) => (t.tstack' = t.tstack + (getTopFrameIndex[t].succ)->sing[0])
}

pred greaterStuff[t : Thread] {
    (t.pc).(OperationList.list) = Greater
    sum[getTopFrameIndex[t]] > 0 --you have enough frames (ie more than 1)

    t.pc' = (t.pc).succ --point to the next place in the program counter
    (sum[getSecondToTopFrameValue[t]] > sum[getTopFrameValue[t]]) => (t.tstack' = t.tstack + (getTopFrameIndex[t].succ)->sing[1])
    (not sum[getSecondToTopFrameValue[t]] > sum[getTopFrameValue[t]]) => (t.tstack' = t.tstack + (getTopFrameIndex[t].succ)->sing[0])
}

pred lessStuff[t : Thread] {
    (t.pc).(OperationList.list) = Less
    sum[getTopFrameIndex[t]] > 0 --you have enough frames (ie more than 1)

    t.pc' = (t.pc).succ --point to the next place in the program counter
    (sum[getSecondToTopFrameValue[t]] < sum[getTopFrameValue[t]]) => (t.tstack' = t.tstack + (getTopFrameIndex[t].succ)->sing[1])
    (not sum[getSecondToTopFrameValue[t]] < sum[getTopFrameValue[t]]) => (t.tstack' = t.tstack + (getTopFrameIndex[t].succ)->sing[0])
}

pred greaterEqualStuff[t : Thread] {
    (t.pc).(OperationList.list) = GreaterEqual
    sum[getTopFrameIndex[t]] > 0 --you have enough frames (ie more than 1)

    t.pc' = (t.pc).succ --point to the next place in the program counter
    (sum[getSecondToTopFrameValue[t]] >= sum[getTopFrameValue[t]]) => (t.tstack' = t.tstack + (getTopFrameIndex[t].succ)->sing[1])
    (not sum[getSecondToTopFrameValue[t]] >= sum[getTopFrameValue[t]]) => (t.tstack' = t.tstack + (getTopFrameIndex[t].succ)->sing[0])
}

pred lessEqualStuff[t : Thread] {
    (t.pc).(OperationList.list) = LessEqual
    sum[getTopFrameIndex[t]] > 0 --you have enough frames (ie more than 1)

    t.pc' = (t.pc).succ --point to the next place in the program counter
    (sum[getSecondToTopFrameValue[t]] <= sum[getTopFrameValue[t]]) => (t.tstack' = t.tstack + (getTopFrameIndex[t].succ)->sing[1])
    (not sum[getSecondToTopFrameValue[t]] <= sum[getTopFrameValue[t]]) => (t.tstack' = t.tstack + (getTopFrameIndex[t].succ)->sing[0])
}

pred ifStuff[t : Thread] {
    (t.pc).(OperationList.list) = If
    sum[getTopFrameIndex[t]] > 1 --you have enough frames (ie more than 2)
    getThirdToTopFrameValue[t] in sing[0] + sing[1]
    sum[getSecondToTopFrameValue[t]] >= 0
    sum[getSecondToTopFrameValue[t]] < #list
    sum[getTopFrameValue[t]] >= 0
    sum[getTopFrameValue[t]] < #list

    (getThirdToTopFrameValue[t] = sing[0]) => (t.pc' = getTopFrameValue[t])
    (getThirdToTopFrameValue[t] = sing[1]) => (t.pc' = getSecondToTopFrameValue[t])
    t.tstack' = pop3[t]
}

pred jumpStuff[t : Thread] {
    (t.pc).(OperationList.list) = Jump
    some t.tstack -- need at least one frame
    sum[getTopFrameValue[t]] >= 0
    sum[getTopFrameValue[t]] < #list

    t.pc' = getTopFrameValue[t] -- change the program counter to the given number
    t.tstack' = pop1[t]
}

pred pushStuff[t : Thread, n : Int] {
    (t.pc).(OperationList.list) in Push
    (t.pc).(OperationList.list).num = n

    t.pc' = (t.pc).succ
    t.tstack' = t.tstack + (getTopFrameIndex[t].succ)->n
}

pred end[t : Thread] {
    (t.pc).(OperationList.list) = END
    some t.done' 
    t.pc' = t.pc
    t.tstack' = t.tstack
}


pred transitionStates {
    always (all t : Thread | {
        addStuff[t]
        or subtractStuff[t]
        or multiplyStuff[t]
        or divideStuff[t]
        or remainderStuff[t]
        or bringStuff[t]
        or sendStuff[t]
        or copyStuff[t]
        or removeStuff[t]
        or swapStuff[t]
        or dropStuff[t]
        or equalStuff[t]
        or lessStuff[t]
        or greaterStuff[t]
        or lessEqualStuff[t]
        or greaterEqualStuff[t]
        or ifStuff[t]
        or jumpStuff[t]
        or (some n : Int | pushStuff[t, n])
        or end[t]
    })
}

pred maxOperations[n: Int] {
    #list <= n
}

pred startValues {
    init
    transitionStates

    some t : Thread | {
        t.tstack[sing[0]] = sing[-5]
        getTopFrameIndex[t] = sing[0]
    }
    
    some t : Thread | {
        t.tstack[sing[0]] = sing[-1]
        getTopFrameIndex[t] = sing[0]
    }
    
    some t : Thread | {
        t.tstack[sing[0]] = sing[0]
        getTopFrameIndex[t] = sing[0]
    }
    
    some t : Thread | {
        t.tstack[sing[0]] = sing[1]
        getTopFrameIndex[t] = sing[0]
    }
    
    some t : Thread | {
        t.tstack[sing[0]] = sing[5]
        getTopFrameIndex[t] = sing[0]
    }
}

-- 0<5,9?d~1*.d.
pred absoluteValue {
    init
    transitionStates

    OperationList.list[sing[0]] in Push && (OperationList.list[sing[0]]).num = sing[0]
    OperationList.list[sing[1]] = Less
    OperationList.list[sing[2]] in Push && (OperationList.list[sing[2]]).num = sing[5]
    OperationList.list[sing[3]] in Push && (OperationList.list[sing[3]]).num = sing[9]
    OperationList.list[sing[4]] = If
    OperationList.list[sing[5]] = Drop
    OperationList.list[sing[6]] in Push && (OperationList.list[sing[6]]).num = sing[-1]
    OperationList.list[sing[7]] = Multiplication
    OperationList.list[sing[8]] = END
    OperationList.list[sing[9]] = Drop
    OperationList.list[sing[10]] = END
    #list = 11
}

run {startValues absoluteValue} for exactly 5 Thread, 23 Operation, 5 Int