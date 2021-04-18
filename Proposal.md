# cs1710-calculator



# Initial project proposal

We would like to attempt to model a very simple stack-based RPN calculator/programming language. Apart from basic arithmetic, we would like to have operations that manipulate the order of the stack, and potentially operations that allow for branching and looping to create more complicated functions. We are interested in this partly because it seems like an interesting challenge, and partly because it provides an opportunity to use Forge (or similar tools) to generate functions/programs for us, rather than just analyzing them.

## Foundation Goal 

We plan to model a stack of memory cells, each containing an integer. There will also be a list of commands which, when the model is run, act on the stack in order. Some of the commands are mathematical functions that operate on numbers at the top of the stack and push the results onto the stack. Other commands can add elements to the stack, move elements of the stack around, remove elements from the stack, and copy elements in the stack. By combining these commands, we can create functions that act on an initial state of the stack (for example, a single input number) and produce output numbers. With these capabilities, there are two types of properties we could check: If we hard code the list of commands, then we have specified a function, and we can let the inputs vary to learn about the function. For example, we could find the bounds of the function, and we could prove certain properties of the output (within the range of integers available). If we hard code the input stack but let the commands vary, then we can learn about what types of numbers are possible to produce from given inputs. We could, for example, check how large a number can be created from given input numbers, perhaps restricted to certain operations. We could also aim for specific numbers, like the 24 game.

## Target Goal 

We intend to create a model with multiple stacks of numbers, and the single list of commands will act on all of them simultaneously. If we specify the original state of each stack, along with the final state of each stack, but do not specify the list of commands that map the initial to final states, we can let Forge find such a list of commands. So, it will be possible to find functions that match arbitrary specifications. It could be interesting to find the *shortest* possible function that matches a given specification, which we could do by varying the bounds on the number of commands.

## Reach Goal 

It could also be possible to create commands that implement control flow. Rather than executing all the commands in order, we could have an instruction pointer that usually proceeds one step at a time but can be moved based on the numbers in the stack. This could allow for more complicated computations, like factorials, Euclid’s algorithm, and prime factorization. The introduction of control flow allows for us to create functions that no longer rely on mathematical operations but directly map inputs to outputs, using a table of “if”s. So, it could be interesting to investigate what types of relations are “non-obvious” enough that the model is predisposed toward creating an if-table rather than a normal mathematical expression.