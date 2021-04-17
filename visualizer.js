div.replaceChildren() // remove all content

let instanceindx = 0
for (i of instances){
    
  const instancename = document.createElement('p')
  instancename.textContent = "Instance " + instanceindx
  instancename.style.marginTop = '18px'
  div.appendChild(instancename)
  
//Rendering the threads (currently only rendering the first thread)...
for (thread of i.signature("Thread").atoms()){
  
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

  thread.join(i.field("tstack")).tuples().forEach(stackTuple => {   
    //Hiding indexes, seems safe to assume elements are in order so
    //there's no need for them...
    //stackIndexes.textContent += stackTuple.join(i.signature("Int")) + "  "
    stackElements.textContent += i.signature("Int").join(stackTuple) + "  "
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


let opList = i.signature("OperationList").join(i.field("list"))
const listText = document.createElement('p')
operationListHolder.appendChild(listText)

opList.tuples().forEach(op => {  
  //Assumes each thread's pc is at the same point...
  const isPushOperation = i.signature("Int").join(op).toString().startsWith("Operation")
  let operationName = ""
  if (isPushOperation){
    const toBePushed = i.signature("Int").join(op).join(i.field("num"))
    operationName = "Push (" + toBePushed + ")"
  }else{
    operationName = i.signature("Int").join(op).toString()
    operationName = operationName.substring(0, operationName.length-1)
  }
  
  const stringifiedOp = op.atoms()[0] + " " + operationName + " -> "
  const isSelected = parseInt(op.atoms()[0].toString()) == parseInt(i.atom("Thread0").join(i.field("pc")).toString())
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