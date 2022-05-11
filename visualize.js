// Updated for 2022 Sterling
// Click the `div` button at the top of script view to 
//   put the `div` variable in scope.

const allinst = instances.map(processInstances)
const numinst = instances.length
//Calculate bitwidth based on number of Int instances
let num_ints = instances[0].signature("Int").atoms().length
const bitwidth = Math.floor(Math.log(num_ints) / Math.LN2) - 1 //Change of base formula for computing log base 2
//Subtract 1 because bitwidth is always one greater than the board size
const max_int = 2 ** (bitwidth)
div.innerHTML = "" //Clear the div

//set font size based on bit width and window horizontal size
let left_sidebar_width = 181
let right_sidebar_width = 350 + 30
let center_width = window.innerWidth - left_sidebar_width - right_sidebar_width
let display_width = Math.floor(center_width / 2) - 10 //Subtract 10 for scrollbar
let fontsize = Math.floor((display_width * 0.5) / (max_int * 2))
//Font sizes that are too huge look silly, so limit font size to a max of 32px
if (fontsize > 32) {
    fontsize = 32
}

for (let idx = 0; idx < numinst; idx++){
    //Create "State X" tile
    let new_p = document.createElement("p")
    new_p.style.textAlign = "center"
    new_p.style.fontWeight = "bold"
    new_p.style.fontSize = "28px"
    new_p.innerHTML = "State" + idx + ":<br>"
    div.innerHTML += new_p.outerHTML
    //Create the actual state board
    div.innerHTML += draw(allinst[idx], idx)
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

function drawCanvas(inst, inst_idx) {
    //returns a canvas colored according to the current instance
    //Unused, because it doesn't work right now
    let canvas = document.createElement("canvas")
    canvas.id = "canvas" + inst_idx
    document.body.appendChild(canvas)
    //canvas.width = display_width * 0.8
    //canvas.height = display_width * 0.8
    canvas = document.getElementById("canvas" + inst_idx)
    let ctx = canvas.getContext("2d")
    for(let x = -max_int; x < max_int; x++){
        for(let y = -max_int; y < max_int; y++){
            if(inst.find(coords => coords[0] == x && coords[1] == y)){
                ctx.fillStyle = '#000000'
                ctx.fillRect((x+max_int) * fontsize, (y+max_int) * fontsize, fontsize, fontsize)
            } else {
                ctx.fillStyle = '#FFFFFF'
                ctx.fillRect((x+max_int) * fontsize, (y+max_int) * fontsize, fontsize, fontsize)
            }
        }
    }
    return canvas.outerHTML
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
    new_div.style.fontFamily = "monospace"
    new_div.style.fontSize = fontsize + "px"
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