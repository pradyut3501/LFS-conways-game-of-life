// Updated for 2022 Sterling
// Click the `div` button at the top of script view to 
//   put the `div` variable in scope.

const allinst = instances.map(processInstances)
const numinst = instances.length
const bitwidth = 3 //TODO: Determine this dynamically
const max_int = 2 ** (bitwidth - 1)
div.innerHTML = "" //Clear the div
//set font size based on bit width and window horizontal size
let left_sidebar_width = 181
let right_sidebar_width = 350 + 30
let center_width = window.innerWidth - left_sidebar_width - right_sidebar_width
let display_width = Math.floor(center_width / 2)
let fontsize = Math.floor((display_width * 0.6) / (max_int * 2)) + "px"

for (let idx = 0; idx < numinst; idx++){
    //create center-aligned <p> element
    let new_p = document.createElement("p")
    new_p.style.textAlign = "center"
    new_p.style.fontWeight = "bold"
    new_p.style.fontSize = "28px"
    new_p.innerHTML = "State" + idx + ":<br>"
    div.innerHTML += new_p.outerHTML
    div.innerHTML += draw(allinst[idx])
    div.innerHTML += "<br>"
}

div.innerHTML = encapsulateWithScrollArea(div.innerHTML)
//Done!

function processInstances(inst) {
    let mappings = inst.field("mappings").tuples()
    coords = []
    for (let idx = 0; idx < mappings.length; idx++){
        //Disgusting, but idk how to unpack it any other way and this one works
        //So I cast mappings to a string, and then split on comma
        let curr_tuple = String(mappings[idx]).split(",")
        let x = curr_tuple[1]
        let y = curr_tuple[2]
        coords.push([x,y])
    }
    return coords
}

function draw(inst) {
    //returns a div full of emojis representing the current instance
    let new_div = document.createElement("div")
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
    new_div.style.fontSize = fontsize
    return new_div.outerHTML
}

function encapsulateWithScrollArea(html) {
    let scroll_area = document.createElement("div")
    scroll_area.style.overflowX = "auto"
    scroll_area.style.overflowY = "auto"
    scroll_area.style.maxHeight = (window.innerHeight - 100) + "px"
    scroll_area.innerHTML = html
    return scroll_area.outerHTML
}