#lang forge

option problem_type temporal
option max_tracelength 5

one sig Board {
    var mappings : set Int -> Int, //If it exists, the cell is 'alive', otherwise dead.
    var stateCounter : one Int
}

pred init {
    Board.stateCounter = 0
}

pred cellAlive[x: Int, y : Int] {
    x->y in Board.mappings
}


pred cellDead[x: Int, y: Int] {
    not{cellAlive[x,y]}
}


fun neighbors[x : Int, y : Int]: one Int {
    let neighbors_coord = ((subtract[x,1]->add[y,1]) + (subtract[x,1]->y) + (subtract[x,1]->subtract[y,1]) + (x->add[y,1]) + (x->subtract[y,1]) + (add[x,1]->add[y,1]) + (add[x,1]->y) + (add[x,1]->subtract[y,1])) | {
        #{Board.mappings & neighbors_coord}
    }
}

pred GameRules {
    all x, y : Int | {
        let neighbors = neighbors[x,y] | {
            cellAlive[x,y] => {
                (neighbors < 2 or neighbors > 3) => {
                    next_state{cellDead[x,y]}
                } else {
                    next_state{cellAlive[x,y]}
                }
            } else {
                (neighbors = 3) => {
                    next_state{cellAlive[x,y]}
                } else {
                    next_state{cellDead[x,y]}
                }
            }
        }
    }
}

pred edgeDeadzone {
    //Deadzone around the edge of the board, to prevent overflow/underflow issues
    some max_int : Int | {
        add[max_int, 1] < max_int
        all a : Int | {
            cellDead[a,max_int]
            cellDead[max_int, a]
        }
    }
}

pred nextStateDifferent {
    not{Board.mappings = Board.mappings'}
}

pred threeUniqueStates {
    not{Board.mappings = Board.mappings'}
    not{Board.mappings = Board.mappings''}
}

pred oscilatorPeriod[i : Int] {
    {subtract[i,1] = Board.stateCounter => Board.stateCounter' = 0 else Board.stateCounter' = add[Board.stateCounter, 1]}
}

pred Beacon {
    all x,y : Int | {
        {(x = -2 and y = 1) or (x = -2 and y = 0) or (x = -1 and y = 1) or (x = 0 and y =-2) or (x = 1 and y =-2) or (x = 1 and y =-1)} => cellAlive[x,y]
        else cellDead[x, y]
    }
}

run {
    init
    always{GameRules}
    always{edgeDeadzone}
    always{nextStateDifferent}
    //always{threeUniqueStates}
    always{oscilatorPeriod[3]}
} for 3 Int