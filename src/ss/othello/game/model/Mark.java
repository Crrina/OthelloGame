package ss.othello.game.model;

/**
 * An enumerated type of the options which the board contains.
 * Either Black (BB), White (WW) or Empty (EMPTY).
 */
public enum Mark {


    /**
     * The mark representing neither player's piece.
     */
    EMPTY,
    /**
     * The Mark representing the White piece in Othello.
     */
    WW,
    /**
     * The Mark representing the Black piece in Othello.
     */
    BB;

    /**
     * Returns the other mark.
     *
     * @return the other mark is this mark is not EMPTY or EMPTY
     */
    //@ ensures this == BB ==> \result == WW && this == WW ==> \result == BB;
    public Mark other() {
        if (this == BB) {
            return WW;
        } else if (this == WW) {
            return BB;
        } else {
            return EMPTY;
        }
    }

}
