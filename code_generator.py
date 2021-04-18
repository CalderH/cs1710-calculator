import re

# Scroll down to the bottom for an explanation

def indent_lines(s, num_spaces):
    return re.sub('^', ' ' * num_spaces, s, flags=re.M)

def stack_state(nums):
    state = ''
    for i in range(len(nums)):
        state += f't.tstack[sing[{i}]] = sing[{nums[i]}]\n'
    state += f'getTopFrameIndex[t] = sing[{len(nums) - 1}]'
    return state

def thread_start(start_stack):
    return f'''some t : Thread | {{
{indent_lines(stack_state(start_stack), 4)}
}}'''

def thread_start_end(start_stack, end_stack):
    return f'''some t : Thread | {{
{indent_lines(stack_state(start_stack), 4)}

    eventually {{
        some t.done
{indent_lines(stack_state(end_stack), 8)}
    }}
}}'''

def start_pred(pred_name, stacks):
    num_non_push_operations = 12
    thread_list = [thread_start(stack) for stack in stacks]
    threads = '\n\n'.join(thread_list)
    
    return f'''pred {pred_name} {{
    init
    transitionStates

{indent_lines(threads, 4)}
}}
'''

#                Math operations:
symbols = {'+': 'Addition',
           '*': 'Multiplication',
           '-': 'Subtraction',
           '/': 'Division',
           '%': 'Remainder',
#                Stack manipulation:
           'b': 'Bring',
           's': 'Send',
           'c': 'Copy',
           'r': 'Remove',
           'x': 'Swap',
           'd': 'Drop',
#                Comparison:
           '=': 'Equal',
           '>': 'Greater',
           '<': 'Less',
           ']': 'GreaterEqual',
           '[': 'LessEqual',
#                Control flow:
           '?': 'If',
           '!': 'Jump',
           '.': 'END'}

num_non_push_operations = len(symbols)

def run_threads_start_end(pred_name, stacks, max_operations, max_pushes):
    thread_list = [thread_start_end(start, stacks[start]) for start in stacks]
    threads = '\n\n'.join(thread_list)
    
    return f'''pred {pred_name} {{
    init
    transitionStates
    maxOperations[{max_operations}]

{indent_lines(threads, 4)}
}}

run {pred_name} for exactly {len(stacks)} Thread, {num_non_push_operations + max_pushes} Operation
'''

def run_function(pred_name, commands, num_threads):
    code = f'''pred {pred_name} {{
    init
    transitionStates

'''
    line_number = 0
    num_pushes = 0
    while commands != '':
        if commands[0] == ' ':
            continue
        elif commands[0] in symbols:
            line = f'OperationList.list[sing[{line_number}]] = {symbols[commands[0]]}'
            code += indent_lines(line, 4) + '\n'
            commands = commands[1:]
        else:
            match = re.match(r'~?\d+,?', commands)
            if match is None:
                break
            num_pushes += 1
            n_str = match.group().strip(',')
            if n_str[0] == '~':
                n_str = '-' + n_str[1:]
            commands = commands[match.end():]
            line = f'OperationList.list[sing[{line_number}]] in Push && (OperationList.list[sing[{line_number}]]).num = sing[{n_str}]'
            code += indent_lines(line, 4) + '\n'
        commands.strip()
        line_number += 1
    if commands != '':
        raise Exception('could not parse')

    code += f'''    #list = {line_number}
}}

run {{{pred_name}}} for exactly {num_threads} Thread, {num_non_push_operations + num_pushes} Operation'''
    return code

pred_name, stacks, max_operations, max_pushes

# start_pred: Specify how each thread should start.
#   Inputs:
#   - the name of the predicate
#   - a list of tuples representing stacks
# run_threads_start_end: Specify how each thread should start and end, with a run statement.
#   Inputs:
#   - the name of the predicate
#   - a dict of tuples->tuples representing how each stack starts and ends
#   - the maximum number of operations allowed
#   - the maximum number of push operations allowed
# run_function: specify what commands should happen, with run statement.
#   Inputs:
#   - the name of the predicate specifying the function
#   - the commands (see note)
#   - the number of threads to run the command for
#   Command syntax:
#   - Each command other than Push is represented by one character
#     - See the “symbols” dict for a full list
#   - Any sequence of digits is a Push of that number
#     - To separate two successive Pushes, use a comma
#       - (For example, 11+ pushes 11 and adds it to the number before, while 1,1+ pushes 1 and 1 and adds them)
#     - To push a negative number, use ~ for the minus sign since - is for subtraction

# output = run_threads_start_end('twentyFour', {(1, 2, 3, 4): (24,)}, 7, 2)
# output = run_function('simpleIf', '3,4?1.', 3)
# output = start_pred('simpleIfStartValues', [(-3,), (0,), (2,)])
# output = run_function('absoluteValue', '0<5,9?d~1*.d.', 1)
# output = start_pred('absoluteValueStartValues', [(-5,), (-1,), (0,), (1,), (5,)])
output = run_threads_start_end('nPlus1TimesN', {(0,): (0,), (1,): (2,), (2,): (6,), (-3,): (6,)}, 5, 1)

print(output)
