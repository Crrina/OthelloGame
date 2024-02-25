package ss.othello.game.model;

/**
 * The interface which models a move
 * in a 2 player board game.
 */
public interface Move {

    /**
     * Returns the mark of the move.
     *
     * @return mark
     */
    /*@
        ensures \result != null;
        pure
    */
    Mark getMark();

    /**
     * Returns the field of the move
     *
     * @return field
     */
    /*@
        pure
    */
    int getField();


    /**
     * Makes the move in the game.
     */
    void move();

    /**
     * Returns the board of the move
     *
     * @return board of the move
     */
    /*@
        ensures \result != null;
        pure
    */
    Board getBoard();


}



