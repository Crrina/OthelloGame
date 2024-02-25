package ss.othello.game.model;


import java.util.List;

/**
 * An interface which models a 2 player board-game.
 */
public interface Game {

    /**
     * Check if the game is over, i.e., there is a winner or no more moves are available.
     *
     * @return whether the game is over
     */
    /*@
        pure;
    */
    boolean isGameover();

    /**
     * Query whose turn it is.
     *
     * @return the player whose turn it is
     */
    /*@
        ensures \result != null;
        pure;
    */
    Player getTurn();

    /**
     * Get the winner of the game. If the game is a draw, then this method returns null.
     *
     * @return the winner, or null if no player is the winner
     */
    /*@
        ensures \result != null;
        pure;
    */
    Player getWinner();

    /**
     * Return all moves that are valid in the current state of the game.
     *
     * @return the list of currently valid moves
     */
    /*@
        ensures (\forall Move m; \result.contains(m); isValidMove(m));
        pure
    */
    List<Move> getValidMoves();

    /**
     * Check if a move is a valid move.
     *
     * @param move the move to check
     * @return true if the move is a valid move
     */
    /*@
        ensures \result <==> (\exists Move m; getValidMoves().contains(m); m.equals(move));
        pure
    */
    boolean isValidMove(Move move);

    /**
     * Perform the move, assuming it is a valid move.
     *
     * @param move the move to play
     */
    //@ requires isValidMove(move);
    void doMove(Move move);

    /**
     * Returns the current board of the game.
     *
     * @return the current board
     */
    Board getBoard();

    /**
     * Returns the mark of the current player.
     *
     * @return the mark of the current player
     */
    Mark getMark();


    /**
     * Returns the integer representing the current player's turn.
     *
     * @return the integer representing the current player's turn.
     */
    int getCurrent();

    /**
     * Changes the value of current.
     *
     * @param current the integer representing the current player's turn
     */
    void setCurrent(int current);

}
