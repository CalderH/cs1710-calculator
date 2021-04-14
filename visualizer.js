div.replaceChildren() // remove all content

let instanceindx = 0
for (i of instances){
  
  //thing = i.project() for some reason this doesn't work...
  
  const instancename = document.createElement('p')
  instancename.textContent = "Instance " + instanceindx
  instancename.style.marginTop = '18px'
  div.appendChild(instancename)
  
//Rendering the threads (currently only rendering the first thread)...
for (thread of Thread.tuples()){
  
  const firstThreadParent = document.createElement('pre')
  firstThreadParent.style.width = '30%'
  firstThreadParent.style.height = '30%'
  firstThreadParent.style.margin = '1%'
  firstThreadParent.style.marginRight = '0'
  firstThreadParent.style.padding = '0.5em'
  firstThreadParent.style.border = '1px solid black'
  firstThreadParent.style.color = 'white'
  firstThreadParent.style["background-color"] = 'gray'
  firstThreadParent.style["grid-template-columns"] = 'auto auto auto auto'
  firstThreadParent.style["flex-direction"] = 'col'
  const stackElements = document.createElement('p')
  firstThreadParent.appendChild(stackElements)
  const stackIndexes = document.createElement('p')
  firstThreadParent.appendChild(stackIndexes)

  thread.join(tstack).tuples().forEach(stackTuple => {   
    stackElements.textContent += stackTuple.join(Int) + "  "
    stackIndexes.textContent += Int.join(stackTuple) + "  "
  });

  const threadParentHolder = document.createElement('div')
  threadParentHolder.style.width = "100%"
  threadParentHolder.style['flex-direction'] = "row" 
  threadParentHolder.appendChild(firstThreadParent) 
  div.appendChild(threadParentHolder)  
}


//Rendering the operations list now...
const operationListHolder = document.createElement('pre')
operationListHolder.style.height = '30%'
operationListHolder.style.margin = '1%'
operationListHolder.style.marginRight = '0'
operationListHolder.style.padding = '0.5em'
operationListHolder.style.border = '1px solid black'
operationListHolder.style.color = 'white'
operationListHolder.style["background-color"] = 'orange'
operationListHolder.style["grid-template-columns"] = 'auto auto auto auto'
operationListHolder.style["flex-direction"] = 'col'

//TODO: need to find a cleaner way to do this
//This actually might not be needed anyways...
const allOperations = Addition.tuples()
      .concat(Copy.tuples())
      .concat(END.tuples())
      .concat(Multiplication.tuples())
      .concat(Push.tuples())
      .concat(Send.tuples())
      .concat(Bring.tuples())
      .concat(Swap.tuples())
      .concat(Subtraction.tuples())

let opList = OperationList.join(list)
const listText = document.createElement('p')
operationListHolder.appendChild(listText)

opList.tuples().forEach(op => {  
  //Assumes each thread's pc is at the same point...
  const isSelected = parseInt(op.atoms()[0].toString()) == parseInt(Thread0.join(pc).toString())
  const stringifiedOp = Int.join(op) + op.atoms()[0] + " -> "
  if (isSelected) listText.innerHTML += '<span style="color: #ff0000">' + stringifiedOp + '</span>'
  else listText.innerHTML += stringifiedOp
});


const holder = document.createElement('div')
holder.style.width = "100%"
holder.style['flex-direction'] = "row" 
holder.appendChild(operationListHolder) 
div.appendChild(holder) 
  
  instanceindx++
}


div.style.overflow = "scroll"