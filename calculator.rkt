#lang forge

option problem_type temporal
option max_tracelength 10

// Represents whether a thread is done
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

// example of valid indices: 0, 1, 2, 3
pred stackIndicesInOrder[thread : Thread]{
    some thread.tstack => { // If there is anything in the stack:
        one (sing[0]).(thread.tstack) // There must be an index 0
        one i : (thread.tstack).Int | { // Everything but the top has a successor
            no (i.succ).(thread.tstack)
        }
    }
    all i : (thread.tstack).univ | {sum[i] >= 0} // No negatives
    ~(thread.tstack).(thread.tstack) in iden // One value for every index
}

pred operationIndicesInOrder{
    some OperationList.list => {
        one (sing[0]).(OperationList.list)
        one i : (OperationList.list).Operation | {
            no (i.succ).(OperationList.list)
        }
    }
    all i : (OperationList.list).univ | {sum[i] >= 0}
    ~(OperationList.list).(OperationList.list) in iden
}

pred init {
    Thread.pc = sing[0] // All program counters start at 0
    some list // There are some operations
    some list.END // There is a termination operation at some point (although it does not necessarily reach it)
    (OperationList.list)[sing[0]] != END // The first operation is not end
    no done // No thread starts in the "done" state
    all t : Thread | stackIndicesInOrder[t]
    operationIndicesInOrder
}


// Helper functions ------------------------------------------------------------------------------

// Note: this function has undefined behavior for an empty stack
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

fun pop1[thread : Thread] : set Int -> Int {
    thread.tstack - (getTopFrameIndex[thread] -> Int)
}

fun pop2[thread : Thread] : set Int -> Int {
    thread.tstack - (getTopFrameIndex[thread] -> Int) - (succ.(getTopFrameIndex[thread]) -> Int)
}

fun pop3[thread : Thread] : set Int -> Int {
    thread.tstack - (getTopFrameIndex[thread] -> Int) - (succ.(getTopFrameIndex[thread]) -> Int) - (succ.succ.(getTopFrameIndex[thread]) -> Int)
}

// Mathematical operations ------------------------------------------------------------------------------

// Pop the top two numbers off the stack, and push their sum onto the stack.
pred addPred[t : Thread] {
    (t.pc).(OperationList.list) = Addition // The program counter is currently pointing to the right type of operation
    sum[getTopFrameIndex[t]] > 0 // Since add takes in two numbers, there must be at least two stack frames

    t.pc' = (t.pc).succ // Program counter increments
    // The top two numbers are removed from the stack, and their sum is pushed onto the stack
    t.tstack' = pop2[t] + (succ.(getTopFrameIndex[t]) -> sing[add[sum[getSecondToTopFrameValue[t]], sum[getTopFrameValue[t]]]])
}

// Pop the top two numbers off the stack, and push their difference onto the stack.
// (The top of the stack is subtracted from the second to top.)
pred subtractPred[t : Thread] {
    (t.pc).(OperationList.list) = Subtraction
    sum[getTopFrameIndex[t]] > 0

    t.pc' = (t.pc).succ
    t.tstack' = pop2[t] + (succ.(getTopFrameIndex[t]) -> sing[subtract[sum[getSecondToTopFrameValue[t]], sum[getTopFrameValue[t]]]])
}

// Pop the top two numbers off the stack, and push their product onto the stack.
pred multiplyPred[t : Thread] {
    (t.pc).(OperationList.list) = Multiplication
    sum[getTopFrameIndex[t]] > 0

    t.pc' = (t.pc).succ
    t.tstack' = pop2[t] + (succ.(getTopFrameIndex[t]) -> sing[multiply[sum[getSecondToTopFrameValue[t]], sum[getTopFrameValue[t]]]])
}

// Pop the top two numbers off the stack, and push their quotient onto the stack.
// (The second to top is divided by the top.)
pred dividePred[t : Thread] {
    (t.pc).(OperationList.list) = Division
    getTopFrameValue[t] != sing[0]
    sum[getTopFrameIndex[t]] > 0 // Cannot divide by zero

    t.pc' = (t.pc).succ
    t.tstack' = pop2[t] + (succ.(getTopFrameIndex[t]) -> sing[divide[sum[getSecondToTopFrameValue[t]], sum[getTopFrameValue[t]]]])
}

// Pop the top two numbers off the stack, and push the remainder (when the second to top is divided by the top) onto the stack.
pred remainderPred[t : Thread] {
    (t.pc).(OperationList.list) = Remainder
    getTopFrameValue[t] != sing[0]
    sum[getTopFrameIndex[t]] > 0 // Cannot divide by zero

    t.pc' = (t.pc).succ
    t.tstack' = pop2[t] + (succ.(getTopFrameIndex[t]) -> sing[remainder[sum[getSecondToTopFrameValue[t]], sum[getTopFrameValue[t]]]])
}

// Stack manipulation operations ------------------------------------------------------------------------------

// Push an arbitrary value onto the stack. This is the only operation that takes an input.
pred pushPred[t : Thread, n : Int] {
    (t.pc).(OperationList.list) in Push
    (t.pc).(OperationList.list).num = n // The Operation must have n as its num.

    t.pc' = (t.pc).succ
    some t.tstack => (t.tstack' = t.tstack + (getTopFrameIndex[t].succ)->n)
    no t.tstack => (t.tstack' = sing[0]->n)
}

// Take the i-th element out of the stack and bring it to the front of the stack.
// Uses the top of the stack for the index i, and pops it off.
// Indexed where the top of the stack *after removing i* is 0, and index increases to the bottom of the stack.
// For example:
// 0 0 0 5 1 1 2 becomes
// 0 0 0 1 1 5
// ("take element 2, counting from the top, and bring it to the top")
pred bringPred[t: Thread] {
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

// Opposite of bring: pop off the index i, then take the last element from the stack and put it into the stack at index i.
// For example:
// 0 0 0 1 1 5 2 becomes
// 0 0 0 5 1 1
pred sendPred[t: Thread] {
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

// Copy the element at index i to the front of the stack.
// For example:
// 0 0 0 5 1 1 2 becomes
// 0 0 0 5 1 1 5
pred copyPred[t: Thread] {
    (t.pc).(OperationList.list) = Copy
    sum[getTopFrameValue[t]] >= 0
    sum[getTopFrameValue[t]] <= subtract[#t.tstack, 2]

    t.pc' = (t.pc).succ
    t.tstack' = pop1[t] + getTopFrameIndex[t]->((t.tstack)[sing[subtract[#t.tstack, sum[getTopFrameValue[t]], 2]]])
}

// Remove the stack element at index i.
// For example:
// 0 0 0 5 1 1 2 becomes
// 0 0 0 1 1
pred removePred[t: Thread] {
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

// Swap the top two stack elements.
pred swapPred[t: Thread] {
    (t.pc).(OperationList.list) = Swap
    sum[getTopFrameIndex[t]] > 0

    t.pc' = (t.pc).succ
    t.tstack' = pop2[t] + (succ.(getTopFrameIndex[t]) -> getTopFrameValue[t]) + (getTopFrameIndex[t] -> getSecondToTopFrameValue[t])
}

// Remove the top element from the stack.
pred dropPred[t: Thread] {
    (t.pc).(OperationList.list) = Drop
    some t.tstack

    t.pc' = (t.pc).succ
    t.tstack' = pop1[t]
}

// Comparison operations ------------------------------------------------------------------------------

// If the top two elements are equal, push 1. If they are not, push 0.
pred equalPred[t : Thread] {
    (t.pc).(OperationList.list) = Equal
    sum[getTopFrameIndex[t]] > 0 // Since equal takes in two numbers, there must be at least two stack frames

    t.pc' = (t.pc).succ
    (getSecondToTopFrameValue[t] = getTopFrameValue[t]) => (t.tstack' = t.tstack + (getTopFrameIndex[t].succ)->sing[1])
    (not getSecondToTopFrameValue[t] = getTopFrameValue[t]) => (t.tstack' = t.tstack + (getTopFrameIndex[t].succ)->sing[0])
}

// If the second to top element is greater than the top element, push 1. Else, push 0.
pred greaterPred[t : Thread] {
    (t.pc).(OperationList.list) = Greater
    sum[getTopFrameIndex[t]] > 0

    t.pc' = (t.pc).succ
    (sum[getSecondToTopFrameValue[t]] > sum[getTopFrameValue[t]]) => (t.tstack' = t.tstack + (getTopFrameIndex[t].succ)->sing[1])
    (not sum[getSecondToTopFrameValue[t]] > sum[getTopFrameValue[t]]) => (t.tstack' = t.tstack + (getTopFrameIndex[t].succ)->sing[0])
}

// If the second to top element is less than the top element, push 1. Else, push 0.
pred lessPred[t : Thread] {
    (t.pc).(OperationList.list) = Less
    sum[getTopFrameIndex[t]] > 0

    t.pc' = (t.pc).succ
    (sum[getSecondToTopFrameValue[t]] < sum[getTopFrameValue[t]]) => (t.tstack' = t.tstack + (getTopFrameIndex[t].succ)->sing[1])
    (not sum[getSecondToTopFrameValue[t]] < sum[getTopFrameValue[t]]) => (t.tstack' = t.tstack + (getTopFrameIndex[t].succ)->sing[0])
}

// If the second to top element is greater than or equal to the top element, push 1. Else, push 0.
pred greaterEqualPred[t : Thread] {
    (t.pc).(OperationList.list) = GreaterEqual
    sum[getTopFrameIndex[t]] > 0

    t.pc' = (t.pc).succ
    (sum[getSecondToTopFrameValue[t]] >= sum[getTopFrameValue[t]]) => (t.tstack' = t.tstack + (getTopFrameIndex[t].succ)->sing[1])
    (not sum[getSecondToTopFrameValue[t]] >= sum[getTopFrameValue[t]]) => (t.tstack' = t.tstack + (getTopFrameIndex[t].succ)->sing[0])
}

// If the second to top element is less than or equal to the top element, push 1. Else, push 0.
pred lessEqualPred[t : Thread] {
    (t.pc).(OperationList.list) = LessEqual
    sum[getTopFrameIndex[t]] > 0

    t.pc' = (t.pc).succ
    (sum[getSecondToTopFrameValue[t]] <= sum[getTopFrameValue[t]]) => (t.tstack' = t.tstack + (getTopFrameIndex[t].succ)->sing[1])
    (not sum[getSecondToTopFrameValue[t]] <= sum[getTopFrameValue[t]]) => (t.tstack' = t.tstack + (getTopFrameIndex[t].succ)->sing[0])
}

// Control flow operations ------------------------------------------------------------------------------

// Third from top: discriminator, to choose which line to go to. Positive number = true, zero or negative = false.
// Second from top: the line to go to if true.
// Top: the line to go to if false.
// Pops all three off when it runs and sets the program counter accordingly.l
pred ifPred[t : Thread] {
    (t.pc).(OperationList.list) = If
    sum[getTopFrameIndex[t]] > 1 // Since if takes in three numbers, there must be at least three stack frames
    // The "if" index is a valid operation index:
    sum[getSecondToTopFrameValue[t]] >= 0
    sum[getSecondToTopFrameValue[t]] < #list
    // The "else" index is a valid operation index:
    sum[getTopFrameValue[t]] >= 0
    sum[getTopFrameValue[t]] < #list

    // If:
    (sum[getThirdToTopFrameValue[t]] > 0) => (t.pc' = getSecondToTopFrameValue[t])
    // Else:
    (sum[getThirdToTopFrameValue[t]] <= 0) => (t.pc' = getTopFrameValue[t])
    t.tstack' = pop3[t]
}

// Set the program counter to the number on the top of the stack, and pop that number off the stack.
pred jumpPred[t : Thread] {
    (t.pc).(OperationList.list) = Jump
    some t.tstack // The stack must have at least one element
    // The index must be a valid operation index:
    sum[getTopFrameValue[t]] >= 0
    sum[getTopFrameValue[t]] < #list

    t.pc' = getTopFrameValue[t] // Change the program counter to the given number
    t.tstack' = pop1[t]
}

// End the computation for this thread.
pred endPred[t : Thread] {
    (t.pc).(OperationList.list) = END
    some t.done' // Set the done flag
    t.pc' = t.pc // Program counter stays the same
    t.tstack' = t.tstack // Stack stays the same
}

---------------------------------------------------------------------------------

pred transitionStates {
    always (all t : Thread | {
        addPred[t]
        or subtractPred[t]
        or multiplyPred[t]
        or dividePred[t]
        or remainderPred[t]
        or bringPred[t]
        or sendPred[t]
        or copyPred[t]
        or removePred[t]
        or swapPred[t]
        or dropPred[t]
        or equalPred[t]
        or lessPred[t]
        or greaterPred[t]
        or lessEqualPred[t]
        or greaterEqualPred[t]
        or ifPred[t]
        or jumpPred[t]
        or (some n : Int | pushPred[t, n])
        or endPred[t]
    })
}

// For better performance, use this to limit how many operations are allowed.
pred maxOperations[n: Int] {
    #list <= n
    #list >= 0 // to prevent overflow
}

// test expect {
//     maintainsOrder: {(init and transitionStates and maxOperations[3]) => (always (all t : Thread | stackIndicesInOrder[t]))} for exactly 1 Thread, 20 Operation is theorem
// }
// We did not get final results from this test, but an equivalent check statement ran for 8 hours without finding a counterexample
// (When it did find counterexamples it took a few seconds)

// Examples ---------------------------------------------------------------------------------

/*
The 24 game. The predicate specifies that the single stack is [1 2 3 4] in the initial state
and [24] in the final state. (Allowing for all stack manipulation and control flow operations
causes it to come up with some weird “cheating” solutions along with the expected multiplication.)

pred twentyFour {
    init
    transitionStates
    maxOperations[7]

    some t : Thread | {
        t.tstack[sing[0]] = sing[1]
        t.tstack[sing[1]] = sing[2]
        t.tstack[sing[2]] = sing[3]
        t.tstack[sing[3]] = sing[4]
        getTopFrameIndex[t] = sing[3]
    
        eventually {
            some t.done
            t.tstack[sing[0]] = sing[24]
            getTopFrameIndex[t] = sing[0]
        }
    }
}

run twentyFour for exactly 1 Thread, 21 Operation, 6 Int
*/

/*
Assume there is one number in the stack. If it is positive, the stack will end up containing
a single 1; if it is zero or negative, the stack will end up empty.

pred simpleIf {
    init
    transitionStates

    OperationList.list[sing[0]] in Push && (OperationList.list[sing[0]]).num = sing[3]
    OperationList.list[sing[1]] in Push && (OperationList.list[sing[1]]).num = sing[4]
    OperationList.list[sing[2]] = If
    OperationList.list[sing[3]] in Push && (OperationList.list[sing[3]]).num = sing[1]
    OperationList.list[sing[4]] = END
    #list = 5
}

pred simpleIfStartValues {
    init
    transitionStates

    some t : Thread | {
        t.tstack[sing[0]] = sing[-3]
        getTopFrameIndex[t] = sing[0]
    }
    
    some t : Thread | {
        t.tstack[sing[0]] = sing[0]
        getTopFrameIndex[t] = sing[0]
    }
    
    some t : Thread | {
        t.tstack[sing[0]] = sing[2]
        getTopFrameIndex[t] = sing[0]
    }
}

run {simpleIfStartValues simpleIf} for exactly 3 Thread, 22 Operation
*/

/*
An absolute value function, tested on five stacks with different starting numbers.

-- Generated from code_generator using “0<5,9?d~1*.d.”
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

pred absoluteValuestartValues {
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

run {absoluteValuestartValues absoluteValue} for exactly 5 Thread, 23 Operation, 5 Int
*/

/*
Given sample inputs and outputs (0->0, 1->2, 2->6, -3->6), figures out the function f(n) = (n + 1) * n.

pred nPlus1TimesN {
    init
    transitionStates
    maxOperations[5]

    some t : Thread | {
        t.tstack[sing[0]] = sing[0]
        getTopFrameIndex[t] = sing[0]
    
        eventually {
            some t.done
            t.tstack[sing[0]] = sing[0]
            getTopFrameIndex[t] = sing[0]
        }
    }
    
    some t : Thread | {
        t.tstack[sing[0]] = sing[1]
        getTopFrameIndex[t] = sing[0]
    
        eventually {
            some t.done
            t.tstack[sing[0]] = sing[2]
            getTopFrameIndex[t] = sing[0]
        }
    }
    
    some t : Thread | {
        t.tstack[sing[0]] = sing[2]
        getTopFrameIndex[t] = sing[0]
    
        eventually {
            some t.done
            t.tstack[sing[0]] = sing[6]
            getTopFrameIndex[t] = sing[0]
        }
    }
    
    some t : Thread | {
        t.tstack[sing[0]] = sing[-3]
        getTopFrameIndex[t] = sing[0]
    
        eventually {
            some t.done
            t.tstack[sing[0]] = sing[6]
            getTopFrameIndex[t] = sing[0]
        }
    }
}

run nPlus1TimesN for exactly 4 Thread, 20 Operation
*/
