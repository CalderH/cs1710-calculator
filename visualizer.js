div.replaceChildren() // remove all content
const showIndexes = false //Turn this to true if you want...

let instanceindx = 0

for (t of Thread.tuples()) {
  
  const threadTitle = document.createElement('p')
  threadTitle.innerHTML = t
  div.appendChild(threadTitle)
  
  for (i of instances) {

    //Rendering the threads (currently only rendering the first thread)...
    for (thread of i.signature("Thread").atoms()) {
      if (thread.toString() != t.toString()) continue

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
        if (showIndexes) stackIndexes.textContent += stackTuple.join(i.signature("Int")) + "  "
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
    operationListHolder.style["background-color"] = 'darkgrey'
    operationListHolder.style["grid-template-columns"] = 'auto auto auto auto'
    operationListHolder.style["flex-direction"] = 'col'


    let opList = i.signature("OperationList").join(i.field("list"))
    const listText = document.createElement('p')
    operationListHolder.appendChild(listText)

    opList.tuples().forEach(op => {
      const isPushOperation = i.signature("Int").join(op).toString().startsWith("Operation")
      let operationName = ""
      if (isPushOperation) {
        const toBePushed = i.signature("Int").join(op).join(i.field("num"))
        operationName = "Push (" + toBePushed + ")"
      } else {
        operationName = i.signature("Int").join(op).toString()
        operationName = operationName.substring(0, operationName.length - 1)
      }

      const stringifiedOp = op.atoms()[0] + " " + operationName + " -> "
      const isSelected = parseInt(op.atoms()[0].toString()) == parseInt(i.atom(t.toString()).join(i.field("pc")).toString())
      if (isSelected) listText.innerHTML += '<span style="color: #ff0000; text-decoration-line: underline;">' + stringifiedOp + '</span>'
      else listText.innerHTML += stringifiedOp
    });


    const holder = document.createElement('div')
    holder.style.width = "100%"
    holder.style['flex-direction'] = "row"
    holder.appendChild(operationListHolder)
    div.appendChild(holder)

  }


  const divider = document.createElement('div')
  divider.style.width = "100%"
  divider.style.height = "2px"
  divider.style["background-color"] = 'black'
  divider.style["margin-top"] = '30px'
  divider.style["margin-bottom"] = '30px'
  div.appendChild(divider)

}

div.style.overflow = "scroll"