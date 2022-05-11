#lang forge

option problem_type temporal
option max_tracelength 5

one sig Board {
    var mappings : set Int -> Int, //If it exists, the cell is 'alive', otherwise dead.
    var stateCounter : one Int
}

pred IntBounds2 {
    //Nothing in here, just for compatibility with old tests
}

pred IntBounds3 {
    //Just for compatibility
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

pred lassoSizeTwo {
    Board.mappings = Board.mappings''
}

pred atLeastTwoDistinctStates {
    not{Board.mappings = Board.mappings'}
}

pred StaystheSame {
    Board.mappings = Board.mappings'
}

//Patterns

pred BlockPattern {
    all x,y : Int | {
        (x = 0 or x = 1) and (y = 0 or y = 1) => cellAlive[x,y]
        else cellDead[x,y]
    }
}

pred ToadPattern {
    all x, y : Int | {
        {(x = -2 and y = 0) or (x = -1 and y = 1) or (x = -1 and y = -2) or (x = 0 and y = 1) or (x = 0 and y = -2)  or (x = 1 and y = -1)} => cellAlive[x,y]
        else cellDead[x,y]
    }
}

pred moldPattern { // Period 4 
    all x, y : Int | {
        {(x = 0 and y = 0) or (x = 1 and y = -1) or (x = 2 and y = 0) or 
        (x = 2 and y = 1) or (x = 1 and y = 2)  or (x = 0 and y = 2) or
        (x = -1 and y = 1) or (x = -2 and y = 0)  or (x = -1 and y = -1) or
        (x = -1 and y = -2) or (x = -2 and y = -1)  or (x = -2 and y = -2) or
        (x = -3 and y = -1) or (x = -3 and y = -2)} => cellAlive[x,y]
        else cellDead[x,y]
    }
}

pred Blinker { // Initial state to generate a Blinker oscillator
    all x,y : Int | {
        {(x = 0 and y = 0) or (x = -1 and y = 0) or (x = 1 and y = 0)} => cellAlive[x,y]
        else cellDead[x,y]
    }
}

pred Beacon {
    all x,y : Int | {
        {(x = -2 and y = 1) or (x = -2 and y = 0) or (x = -1 and y = 1) or (x = 0 and y =-2) or (x = 1 and y =-2) or (x = 1 and y =-1)} => cellAlive[x,y]
        else cellDead[x,y]
    }
}

//Tests

test expect {
    vacuityTest: {
        GameRules
    } for 3 Int is sat

    vacuity2Test: {
        always{GameRules} => {}
    } for 3 Int is theorem

    oneLoneCellDies: {
        {always{GameRules} and 
        (all x,y : Int | {
            x = 0 and y = 0 => {cellAlive[x,y]}
            else {cellDead[x,y]}
        } and always{GameRules})} => {
            next_state{
                all x,y: Int | cellDead[x,y]
            }
        }
    } for 3 Int is theorem

    cubeIsStable: {
        (BlockPattern and always{IntBounds2} and always{GameRules}) implies always{BlockPattern}
    } for 3 Int is theorem

    lessThanTwoNeighborsDies: {
        always{GameRules} implies
        {all x, y : Int | {
            (cellAlive[x,y] and neighbors[x,y] < 2) implies next_state cellDead[x,y]
        }}
    } for 3 Int is theorem

    twoOrThreeNeighborsLives: {
        {always{GameRules}} implies
        {all x, y : Int | {
            (cellAlive[x,y] and (neighbors[x,y] = 2 or neighbors[x,y] = 3)) implies next_state cellAlive[x,y]
        }}
    } for 3 Int is theorem

    moreThanThreeNeighborsDies: {
        always{GameRules} implies
        {all x, y : Int | {
            (cellAlive[x,y] and neighbors[x,y] > 3) implies next_state cellDead[x,y]
        }}
    } for 3 Int is theorem

    threeNeighborsBecomesAlive: {
        always{GameRules} implies
        {all x, y : Int | {
            {(x >= -2) and (x <= 1) and (y >= -2) and (y <= 1)} implies
                {(cellDead[x,y] and neighbors[x,y] = 3) implies next_state cellAlive[x,y]}
        }}
    } for 3 Int is theorem

    notThreeNeighborsRemainsDead: {
        always{GameRules} implies
        {all x, y : Int | {
            (cellDead[x,y] and neighbors[x,y] != 3) implies next_state cellDead[x,y]
        }}
    } for 3 Int is theorem

    allDeadRemainDead: {
        always{GameRules} implies {
        {all x, y : Int | {
            cellDead[x,y]
        }} implies next_state always{
            {all x, y : Int | {
            cellDead[x,y]
          }}
        }}
    } for 3 Int is theorem

    blinkerFormsOscillator: {
        always{GameRules} implies {
            Blinker implies always{lassoSizeTwo}
        }
    } for 3 Int is theorem

    lassoTest: {
        one b1:Board | {
            always{GameRules}
            always{IntBounds3}
            mappings = b1 -> 0 -> 0 + b1 -> -1 -> 0 + b1 -> 1 -> 0
            always{lassoSizeTwo}
        } 
    } for 4 Int is sat

    allStaySameTest: {
        one b1:Board | {
            always{GameRules}
            always{IntBounds2}
            mappings = b1 -> -2 -> -2 + b1 -> -2 -> -1 + b1 -> -2 -> 0 + b1 -> -2 -> 1 + b1 -> -1 -> -2 + b1 -> -1 -> -1 + b1 -> -1 -> 0 + b1 -> -1 -> 1 + b1 -> 0 -> -2 + b1 -> 0 -> -1 + b1 -> 0 -> 0 + b1 -> 0 -> 1 + b1 -> 1 -> -2 + b1 -> 1 -> -1 + b1 -> 1 ->  0 + b1 -> 1 -> 1
            always{StaystheSame}
        } 
    } for 3 Int is sat 

    diagonalTest: {
        one b1:Board | {
            always{GameRules}
            always{IntBounds3}
            mappings = b1 -> -2 -> -2 + b1 -> -1 -> -1 + b1 -> 0 -> 0 + b1 -> 1 -> 1
            mappings' = b1 -> -1 -> -1 + b1 -> 0 -> 0
            no mappings''
        } 
    }for 4 Int is sat 

    dyingAndBeingBornTest: {
        one b1:Board | {
            always{GameRules}
            always{IntBounds3}
            mappings =  b1 -> 0 -> 0 + b1 -> 2 -> 0 + b1 -> 1 -> -1 
            mappings' = b1 -> 1 -> -1
            no mappings''
        } 
    } for 4 Int is sat 

    noMappingGetsAMappingTest: {
        one b1:Board | {
            always{GameRules}
            always{IntBounds2}
            no mappings
            next_state mappings = b1 -> -2 -> -2
        } 
    } for 3 Int is unsat 

    mappingChange: {
        one b1:Board | {
            always{GameRules}
            always{IntBounds2}
            no mappings
            next_state mappings = b1 -> -2 -> -2
        } 
    } for 3 Int is unsat 

    overPopulationDoesntKillTest: {
        one b1:Board | {
            always{GameRules}
            always{IntBounds3}
            mappings = b1 -> -1 -> -1 + b1 -> 0 -> 0 + b1 -> 1 -> 1 + b1 -> 1 -> -1 + b1 -> -1 -> 1 
            mappings' = mappings
        } 
    } for 4 Int is unsat 

    threePopulationDoesntBuildTest: {
        one b1:Board | {
            always{GameRules}
            always{IntBounds3}
            mappings =  b1 -> 0 -> 0 + b1 -> 2 -> 0 + b1 -> 1 -> -2 
            no mappings'
        } 
    } for 4 Int is unsat
}

run {
    init
    always{GameRules}
    always{edgeDeadzone}
    lassoSizeTwo
    atLeastTwoDistinctStates
} for 4 Int