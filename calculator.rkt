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
one sig Addition, Multiplication, Subtraction, Division, Remainder extends Operation {}
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
    no sing[-1].(thread.tstack) // No negatives
    ~(thread.tstack).(thread.tstack) in iden // One value for every index
}

pred operationIndicesInOrder{
    one (sing[0]).(OperationList.list)
    one i : (OperationList.list).Operation | {
        no (i.succ).(OperationList.list)
    }
    no sing[-1].(OperationList.list)
    ~(OperationList.list).(OperationList.list) in iden
}


pred init {
    Thread.pc = sing[0]
    some list
    some list.END
    (OperationList.list)[sing[0]] != END
    #list > 0 // no overflow
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

//TODO: How can we make a popn?

fun pop2[thread : Thread] : set Int -> Int {
    thread.tstack - (getTopFrameIndex[thread] -> Int) - (succ.(getTopFrameIndex[thread]) -> Int)
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
        or (some n : Int | pushStuff[t, n])
        or end[t]
    })
}

pred maxOperations[n: Int] {
    #list <= n
}


pred testing {
    init
    transitionStates
    maxOperations[5]

    some t : Thread | {
        getTopFrameValue[t] = sing[0]
        getTopFrameIndex[t] = sing[0]

        eventually {
            some t.done
            getTopFrameValue[t] = sing[1]
            getTopFrameIndex[t] = sing[0]
        }
    }

    some t : Thread | {
        getTopFrameValue[t] = sing[1]
        getTopFrameIndex[t] = sing[0]

        eventually {
            some t.done
            getTopFrameValue[t] = sing[3]
            getTopFrameIndex[t] = sing[0]
        }
    }

    some t : Thread | {
        getTopFrameValue[t] = sing[3]
        getTopFrameIndex[t] = sing[0]

        eventually {
            some t.done
            getTopFrameValue[t] = sing[7]
            getTopFrameIndex[t] = sing[0]
        }
    }

    some t : Thread | {
        getTopFrameValue[t] = sing[-2]
        getTopFrameIndex[t] = sing[0]

        eventually {
            some t.done
            getTopFrameValue[t] = sing[-3]
            getTopFrameIndex[t] = sing[0]
        }
    }
}

run {testing} for exactly 4 Thread, 10 Operation