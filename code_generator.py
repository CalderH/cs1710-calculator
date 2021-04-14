import re

def indent_lines(s, num_spaces):
    return re.sub('^', ' ' * num_spaces, s, flags=re.M)

def stack_state(nums):
    state = ''
    for i in range(len(nums)):
        state += f't.tstack[sing[{i}]] = sing[{nums[i]}]\n'
    state += f'getTopFrameIndex[t] = sing[{len(nums) - 1}]'
    return state

def thread_start_end(start_stack, end_stack):
    return f'''some t : Thread | {{
{indent_lines(stack_state(start_stack), 4)}

    eventually {{
        some t.done
{indent_lines(stack_state(end_stack), 8)}
    }}
}}'''

def run_threads_start_end(pred_name, stacks, max_operations, max_pushes):
    num_non_push_operations = 12
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

stacks = {(0, 0): (0,),
          (0, 1): (2,),
          (1, 1): (4,),
          (-2, -1): (-6,)}
test = run_threads_start_end('sum_and_double', stacks, 4, 1)
# sum_and_double is the name of the predicate
# stacks is the beginning and end state of each stack
# 4 is the maximum allowed number of operations
# 1 is the maximum allowed number of pushes
print(test)