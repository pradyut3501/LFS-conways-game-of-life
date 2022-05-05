#lang forge

option problem_type temporal
option max_tracelength 5

/*
abstract sig Boolean{}
one sig True extends Boolean{}
one sig False extends Boolean{}

sig Cell{
    alive : one Boolean
}
*/
one sig Cell{}

one sig Board {
    var mappings : pfunc Int -> Int -> Cell //If it exists, the cell is 'alive', otherwise dead.
}

fun neighbors[x : Int, y : Int]: one Int {
    #{a, b: Int | 
    // not((a < 0) and (x > add[1, a])) and //subtraction overflow
    // not((a > 0) and (x < add[-2, a])) and 
    // not((b < 0) and (y > add[1, b])) and 
    // not((b > 0) and (y < add[-2, b])) and 
    // not((a > 0) and (x > subtract[3, a])) and // addition overflow
    // not((a < 0) and (x < subtract[-4, a])) and
    // not((b > 0) and (y > subtract[3, b])) and
    // not((b < 0) and (y < subtract[-4, b])) and
    (abs[subtract[x,a]] <= 1) and (abs[subtract[y,b]] <= 1) and (not{a = x and b = y}) and some Board.mappings[a][b]}

    // let neighbors_coord = (subtract[x,1]->add[y,1]) + (subtract[x,1]->y) + (subtract[x,1]->subtract[y,1]) + (x->add[y,1]) + (x->subtract[y,1]) + (add[x,1]->add[y,1]) + (add[x,1]->y) + (add[x,1]->subtract[y,1]) | {
    //     //#{a,b : neighbors_coord | some Board.mappings[a][b]}
    //     #{a : neighbors_coord | some Board.mappings[a[0]][a[1]]}
    // }
    //(abs[subtract[x,a]] <= 1) and (abs[subtract[y,b]] <= 1) and (not{a = x and b = y}) and
}

pred IntBounds3 {
    all x : Int | {
        ((x >= 4) or (x < -4)) implies {
            all y: Int | no Board.mappings[x][y] and no Board.mappings[y][x] 
        }
    }
}

pred IntBounds2 {
    all x : Int | {
        ((x >= 2) or (x < -2)) implies {
            all y: Int | no Board.mappings[x][y] and no Board.mappings[y][x] 
        }
    }
}

fun validInt2[x : Int, y : Int]: one Boolean {
    (x < 2) and (x >= -2) and (y < 2) and (y >= -2)
}

fun validInt3[x : Int, y : Int]: one Boolean {
    (x < 4) and (x >= -4) and (y < 4) and (y >= -4)
}

pred GameRules {
    all x, y : Int | {
        validInt3[x, y] implies {
            let neighbors = neighbors[x,y] | {
                some Board.mappings[x][y] => {
                    (neighbors < 2 or neighbors > 3) => {
                        next_state{no Board.mappings[x][y]}
                    } else {
                        next_state{some Board.mappings[x][y]}
                    }
                } else {
                    (neighbors = 3) => {
                        next_state{some Board.mappings[x][y]}
                    } else {
                        next_state{no Board.mappings[x][y]}
                    }
                }
            }
        }
    }
}

expect {

    vacuity: {
        GameRules
    } is sat

    vacuity2: {
        always{GameRules} => {}
    } is theorem

    oneLoneCellDies: {
        (all x,y : Int | {
            x = 0 and y = 0 => {some Board.mappings[x][y]}
            else {no Board.mappings[x][y]}
        } and always{GameRules}) => {
            next_state{
                all x,y: Int | no Board.mappings[x][y]
            }
        }
    } for 2 Int is theorem

    /*cubeIsStable: {
        all x,y : Int | {
                (x = 0 or x = 1) and (y = 0 or y = 1) => some Board.mappings[x][y]
                else no Board.mappings[x][y]
        } and always{GameRules} => {
            always {
                all x,y : Int | {
                    (x = 0 or x = 1) and (y = 0 or y = 1) => some Board.mappings[x][y]
                    else no Board.mappings[x][y]
                }
            }
        }
    } is theorem */
}

pred Blinker { // Initial state to generate a Blinker oscillator
    all x,y : Int | {
        {(x = 0 and y = 0) or (x = -1 and y = 0) or (x = 1 and y = 0)} => some Board.mappings[x][y]
        else no Board.mappings[x][y]
    }
}

pred Beacon {
    all x,y : Int | {
        {(x = -2 and y = 1) or (x = -2 and y = 0) or (x = -1 and y = 1) or (x = 0 and y =-2) or (x = 1 and y =-2) or (x = 1 and y =-1)} => some Board.mappings[x][y]
        else no Board.mappings[x][y]
    }
}

pred atLeastTwoDistinctStates {
    some x, y : Int | {
        Board.mappings[x][y] != Board.mappings'[x][y]
    }
}

pred lassoSizeTwo {
    // To be meaningful, this needs to be run with atLeastTwoDistinctStates
    all x, y : Int | {
        Board.mappings[x][y] = Board.mappings''[x][y]
    }
}

pred lassoSizeThree {
    // To be meaningful, this needs to be run with atLeastTwoDistinctStates
    all x, y : Int | {
        Board.mappings[x][y] = Board.mappings'''[x][y]
    }
}

run {
    // all x,y : Int | {
    //     (x = 0 or x = 1) and (y = 0 or y = 1) => some Board.mappings[x][y]
    //     else no Board.mappings[x][y]
    // } and always{GameRules}
    always{IntBounds3}
    //Beacon
    atLeastTwoDistinctStates
    // lassoSizeTwo
    always{GameRules}
} for 4 Int