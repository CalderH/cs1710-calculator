import re

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

num_non_push_operations = 12

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

def run_function(pred_name, commands):
    symbols = {'+': 'Addition',
               '*': 'Multiplication',
               '-': 'Subtraction',
               '/': 'Division',
               '%': 'Remainder',
               'b': 'Bring',
               's': 'Send',
               'c': 'Copy',
               'r': 'Remove',
               'x': 'Swap',
               'd': 'Drop',
               '.': 'END'}

    code = f'pred {pred_name} {{\n'
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

run {{{pred_name}}} for exactly [number] Thread, {num_non_push_operations + num_pushes} Operation'''
    return code



# start_pred: specify how each thread should start
# run_threads_start_end: specify how each thread should start and end, with run statement
# run_function: specify what commands should happen, with run statement

# syntax for run_function:
# each command other than Push is represented by one character; see the list in the function definition
# any sequence of digits is Pushed as a number; to separate two successive Pushes use a comma
# (e.g. 11+ pushes 11 and adds, while 1,1+ pushes 1 and 1 and adds them)
# to push a negative number, use ~ for the minus sign since - is for subtraction

test = run_function('x_times_x_plus_1', '0c1+*.')
print(test)