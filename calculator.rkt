#lang forge

option problem_type temporal
option max_tracelength 10

one sig DoneFlag {}

sig Thread {
    var tstack: set Int -> Int, //index -> value, bottom of the stack is index 0
    var pc: one Int, //PC is program counter
    var done: lone DoneFlag
} 

abstract sig Operation {}
one sig Addition extends Operation {}
one sig END extends Operation {} //Points to itseelf as an end...

//Nothing is var here; nothing changes
one sig OperationList {
	list : set Int -> Operation  //index -> Operation, but the top of the list is 0
}

//TODO: what about bit overflow
pred indexesInOrder[thread : Thread]{
    one thread.tstack.(sing[0]) // Must have 0
    one i : thread.tstack.Int | {
        no thread.tstack.(sing[add[sum[i], 1]])
    }
    ~(thread.tstack).(thread.tstack) in iden //Only value for every index
}

pred indexesInOrderOperations{
    one OperationList.list.(sing[0]) // Must have 0
    one i : OperationList.list.Int | {
        no OperationList.list.(sing[add[sum[i], 1]])
    }
    ~(OperationList.list).(OperationList.list) in iden //Only value for every index
}


pred init {
    Thread.pc = sing[0]
    some list
    some list.END
    no done
    // all t : Thread | some t.tstack
    all t : Thread | indexesInOrder[t]
    indexesInOrderOperations
}


----------------------------------------

fun getTopFrameIndex[thread : Thread] : one Int {
    sing[max[thread.tstack.Int]]
}

fun getTopFrameValue[thread : Thread] : one Int {
    thread.tstack[getTopFrameIndex[thread]]
}

//TODO: How can we make a popn?

fun pop2[thread : Thread] : set Int -> Int {
    thread.tstack - (getTopFrameIndex[thread] -> Int) - (succ.(getTopFrameIndex[thread]) -> Int)
}

//GOing to be using imprecise syntax for Int and int aruthmetic since its annoying
pred addStuff[t : Thread] {
    (t.pc).(OperationList.list) = Addition
    sum[getTopFrameIndex[t]] > 1 --you have enough frames (ie more than 1)
    t.pc' = (t.pc).succ --point to the next place in the program counter
    
    t.tstack' = pop2[t] + (succ.(getTopFrameIndex[t]) -> sing[add[sum[getTopFrameValue[t]], sum[t.tstack[succ.(getTopFrameIndex[t])]]]])
}


pred end[t : Thread] {
    (t.pc).(OperationList.list) = END
    some t.done' 
    t.pc' = t.pc
    t.tstack' = t.tstack
}


pred transitionStates {
    always (all t : Thread | {
        addStuff[t] or end[t]
    })
}