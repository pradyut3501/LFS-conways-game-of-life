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
    let neighbors_coord = (subtract[x,1]->add[y,1]) + (subtract[x,1]->y) + (subtract[x,1]->subtract[y,1]) + (x->add[y,1]) + (x->subtract[y,1]) + (add[x,1]->add[y,1]) + (add[x,1]->y) + (add[x,1]->subtract[y,1]) | {
        #{a,b : neighbors_coord | some Board.mappings[a][b]}
    }
    //(abs[subtract[x,a]] <= 1) and (abs[subtract[y,b]] <= 1) and (not{a = x and b = y}) and
}

pred GameRules {
    all x, y : Int | {
        let neighbors = neighbors[x,y] | {
            some Board.mappings[x][y] => {
                (neighbors < 2 or neighbors > 3) => {
                    next_state{no Board.mappings[x][y]}
                }else {
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

run {
    all x,y : Int | {
        (x = 0 or x = 1) and (y = 0 or y = 1) => some Board.mappings[x][y]
        else no Board.mappings[x][y]
    } and always{GameRules}
} for 3 Int