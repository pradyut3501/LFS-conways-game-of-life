// Updated for 2022 Sterling
// Click the `div` button at the top of script view to 
//   put the `div` variable in scope.

const allinst = instances.map(processInstances)
const numinst = instances.length
const max_int = 4 //instances[0].signature("Int").atoms().length
div.innerHTML = "" //Clear the div

for (let idx = 0; idx < numinst; idx++){
    div.innerHTML += "State " + idx + ":<br>"
    draw(allinst[idx])
    verticalSpace()
}

function processInstances(inst) {
    let mappings = inst.field("mappings").tuples()
    coords = []
    //alert(String(mappings[1]).split(","))
    for (let idx = 0; idx < mappings.length; idx++){
        let curr_tuple = String(mappings[idx]).split(",")
        let x = curr_tuple[1]
        let y = curr_tuple[2]
        coords.push([x,y])
    }
    //alert(coords)
    return coords
}

function draw(inst) {
    //This is temporary: Eventually will be replaced with actual drawing stuff
    new_div = document.createElement("div")
    for(let x = -max_int; x < max_int; x++){
        for(let y = -max_int; y < max_int; y++){
            if(inst.find(coords => coords[0] == x && coords[1] == y)){
                new_div.innerHTML += "⬛"
            } else {
                new_div.innerHTML += "⬜"
            }
        }
        new_div.innerHTML += "<br>"
    }
    //new_div.innerHTML += "\n\n END OF STATE \n\n"
    div.innerHTML += new_div.innerHTML
}

function verticalSpace(){
    div.innerHTML += "<br><br>"
}