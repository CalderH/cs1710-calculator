from typing import List, Optional, Tuple
from abc import ABC, abstractmethod
import re

class StackException(Exception):
    pass

Stack = List[int]

class State:
    pass

class Instruction:
    pass

Program = List[Instruction]

class State:
    def __init__(self, stack: Stack, program: Program):
        self.stack: Stack = stack
        self.pc: int = 0
        self.program: Program = program

class Instruction(ABC):
    def __init__(self, name: str):
        self.name = name
    
    def check(self, state: State):
        pass
    
    def update_pc(self, state: State):
        pass

    def manipulate_stack(self, stack: Stack):
        pass

    def remove_inputs(self, stack: Stack, num_to_remove: int):
        stack = stack[:-num_to_remove]

    def do(self, state: State):
        self.check(state)
        self.update_pc(state)
        self.manipulate_stack(state.stack)

    def __repr__(self):
        return self.name

class SkipInstruction(Instruction):
    def update_pc(self, state):
        state.pc += 1
    
class InputInstruction(Instruction):
    def __init__(self, name: str, num_inputs: int):
        super().__init__(name)
        self.num_inputs = num_inputs

    def check(self, state: State):
        if len(state.stack) < self.num_inputs:
            raise StackException(f'The {self.name} instruction requires {self.num_inputs} inputs.')

class Stop(Instruction):
    symbol = '.'
    
    def __init__(self):
        super().__init__('stop')

    def check(self, state: State):
        pass

    def update_pc(self, state: State):
        pass

    def manipulate_stack(self, stack: Stack):
        pass

class Add(InputInstruction, SkipInstruction):
    symbol = '+'
    
    def __init__(self):
        super().__init__('add', 2)

    def manipulate_stack(self, stack: Stack):
        a = stack.pop()
        b = stack.pop()
        stack.append(a + b)

class Subtract(InputInstruction, SkipInstruction):
    symbol = '-'
    
    def __init__(self):
        super().__init__('subtract', 2)

    def manipulate_stack(self, stack: Stack):
        a = stack.pop()
        b = stack.pop()
        stack.append(b - a)

class Multiply(InputInstruction, SkipInstruction):
    symbol = '*'
    
    def __init__(self):
        super().__init__('multiply', 2)

    def manipulate_stack(self, stack: Stack):
        a = stack.pop()
        b = stack.pop()
        stack.append(a * b)

class Divide(InputInstruction, SkipInstruction):
    symbol = '/'
    
    def __init__(self):
        super().__init__('divide', 2)

    def manipulate_stack(self, stack: Stack):
        a = stack.pop()
        b = stack.pop()
        stack.append(b // a)

class Remainder(InputInstruction, SkipInstruction):
    symbol = '%'
    
    def __init__(self):
        super().__init__('remainder', 2)

    def manipulate_stack(self, stack: Stack):
        a = stack.pop()
        b = stack.pop()
        stack.append(b % a)

class Push(SkipInstruction):
    def __init__(self, n: int):
        super().__init__('push')
        self.n = n
    
    def manipulate_stack(self, stack: Stack):
        stack.append(self.n)

    def __repr__(self):
        return f'push {self.n}'

class Drop(InputInstruction, SkipInstruction):
    symbol = 'd'
    
    def __init__(self):
        super().__init__('drop', 1)
    
    def manipulate_stack(self, stack: Stack):
        stack.pop()

class Bring(InputInstruction, SkipInstruction):
    symbol = 'b'
    
    def __init__(self):
        super().__init__('bring', 1)

    def manipulate_stack(self, stack: Stack):
        i = stack.pop()
        try:
            to_move = stack[-i]
            del stack[-i]
            stack.append(to_move)
        except IndexError:
            raise StackException('Index error in bring')

class Send(InputInstruction, SkipInstruction):
    symbol = 's'
    
    def __init__(self):
        super().__init__('send', 2)

    def manipulate_stack(self, stack: Stack):
        i = stack.pop()
        to_move = stack.pop()
        try:
            stack.insert(i + 1, to_move)
        except IndexError:
            raise StackException('Index error in send')

class Copy(InputInstruction, SkipInstruction):
    symbol = 'c'
    
    def __init__(self):
        super().__init__('copy', 1)

    def manipulate_stack(self, stack: Stack):
        i = stack.pop()
        try:
            to_copy = stack[-i]
            stack.append(to_copy)
        except IndexError:
            raise StackException('Index error in copy')

class Jump(InputInstruction):
    symbol = 'j'
    
    def __init__(self):
        super().__init__('jump', 1)
    
    def update_pc(self, state: State):
        x = state.stack[-1]
        if x >= len(state.program):
            raise StackException('Invalid program counter in jump')
        state.pc = x
    
    def manipulate_stack(self, stack: Stack):
        stack.pop()

class If(InputInstruction):
    symbol = 'i'
    
    def __init__(self):
        super().__init__('if', 3)
    
    def update_pc(self, state: State):
        b = state.stack[-3]
        i = state.stack[-2]
        e = state.stack[-1]
        x = i
        if b == 0:
            x = e
        if x >= len(state.program):
            raise StackException('Invalid program counter in jump')
        state.pc = x
    
    def manipulate_stack(self, stack: Stack):
        stack.pop()
        stack.pop()
        stack.pop()
    
class Equals(InputInstruction, SkipInstruction):
    symbol = '='
    
    def __init__(self):
        super().__init__('equals', 2)
    
    def manipulate_stack(self, stack: Stack):
        a = stack[-1]
        b = stack[-2]
        if a == b:
            stack.append(1)
        else:
            stack.append(0)

def parse(s: str) -> Program:
    instructions = [Stop, Add, Subtract, Multiply, Divide, Remainder, Drop, Bring, Send, Copy, Jump, If, Equals]
    symbol_dict = {i.symbol: i for i in instructions}
    program: Program = []

    while s != '':
        print(s)
        if s[0] in symbol_dict:
            program.append(symbol_dict[s[0]]())
            s = s[1:]
        else:
            match = re.match(r'\d+,?', s)
            if match is None:
                break
            n_str = match.group().strip(',')
            s = s[match.end():]
            program.append(Push(int(n_str)))
        s.strip()
    if s != '':
        raise Exception('could not parse')
    return program

def run(program: Program, init_stack: Stack):
    state: State = State(init_stack, program)
    while True:
        print(state.stack)
        if state.pc >= len(program):
            break
        instruction: Instruction = program[state.pc]
        if isinstance(instruction, Stop):
            break
        instruction.do(state)

p = parse('=4,6i4.7')
print(p)

# s = [3, 5]
# run(p, s)