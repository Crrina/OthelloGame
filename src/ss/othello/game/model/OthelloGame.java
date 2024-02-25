package ss.othello.game.model;


import java.util.ArrayList;
import java.util.List;

/**
 * This class implements the Game interface to
 * represent a game of Othello.
 * Players can make moves and flip opponent pieces by trapping
 * them.
 */
public class OthelloGame implements Game {
    /*@
     public invariant !isGameover() ==> getValidMoves().size() > 0;
     public invariant !isGameover() ==> getTurn() != null;
     private invariant this.current == 0 || this.current == 1;
    */

    /**
     * The board of the game.
     */
    private Board board;


    /**
     * The players of the game.
     */
    private Player[] players;


    /**
     * Index of the current player.
     */
    private int current;


    /**
     * Creates the game.
     *
     * @param player1 the first player.
     * @param player2 the second player.
     */
    /*@
        requires player1 != null && player2 != null;
        ensures players[0] == player1 && players[1] == player2;
    */
    public OthelloGame(Player player1, Player player2) {
        board = new Board();
        current = 0;
        players = new Player[2];
        players[0] = player1;
        players[1] = player2;

    }

    /**
     * Check if the game is over, i.e., there is a winner, no more moves are available
     * or the board is full.
     *
     * @return true if the game is over.
     */
    /*@
        ensures \result == board.gameOver();
        pure
    */
    @Override
    public boolean isGameover() {
        return board.gameOver();
    }

    /**
     * Query whose turn it is.
     *
     * @return the Player whose turn it is.
     */
    /*@
        ensures this.current == 0 ==> \result == players[0];
        ensures this.current != 0 ==> \result == players[1];
        pure;
    */
    @Override
    public Player getTurn() {
        if (this.current == 0) {
            return players[0];
        } else {
            return players[1];
        }
    }

    /**
     * Get the winner of the game. If the game is a draw, then this method returns null.
     *
     * @return the Player who is the winner, or null if no player is the winner
     */
    /*@
        ensures board.hasWinner() && board.isWinner(Mark.BB) ==> \result == players[0];
        ensures board.hasWinner() && board.isWinner(Mark.WW) ==> \result == players[1];
        pure
    */
    @Override
    public Player getWinner() {
        if (board.hasWinner()) {
            if (board.isWinner(Mark.BB)) {
                return players[0];
            }
            if (board.isWinner(Mark.WW)) {
                return players[1];
            }
        }
        return null;
    }

    /**
     * Return all moves that are valid in the current state of the game.
     *
     * @return the list of currently valid moves.
     */
    /*@
        ensures (\forall int i; i < board.getDim() * board.getDim()
        && board.calculateValidMoves(getMark()).containsKey(i);
         \result.contains(new OthelloMove(getMark(), i, board)));
         pure
    */
    @Override
    public List<Move> getValidMoves() {
        List<Move> validMoves = new ArrayList<>();
        if (!board.gameOver()) {
            for (int i = 0; i < board.getDim() * board.getDim(); i++) {
                if (board.calculateValidMoves(getMark()).containsKey(i)) {
                    validMoves.add(new OthelloMove(getMark(), i, board));
                }
            }
        }
        return validMoves;
    }

    /**
     * Check if a move is a valid move.
     * The move is valid if the index of this move
     * is contained in the method calculateValidMoves.
     *
     * @param move the move to check
     * @return true if the move is a valid move
     */
    /*@
        requires move != null;
        ensures move.getMark() == getMark() ==> \result ==
        board.calculateValidMoves(getMark()).containsKey(move.getField());
        pure
    */
    @Override
    public boolean isValidMove(Move move) {
        Mark mark = getMark();
        if (move.getMark() == mark) {
            return board.calculateValidMoves(mark).containsKey(move.getField());
        }

        return false;
    }

    /**
     * Perform the move, assuming it is a valid move
     * and change the turn of the player.
     *
     * @param move the move to play
     */
    /*@
        requires isValidMove(move);
        ensures \old(current) == 0 ==> current == 1;
        ensures \old(current) != 0 ==> current == 0;
    */
    @Override
    public void doMove(Move move) {
        move.move();
        if (current == 0) {
            current = 1;
        } else {
            current = 0;
        }
    }

    /**
     * Returns the mark of the current player.
     *
     * @return the mark of the current player
     */
    /*@
        ensures \result.equals(Mark.BB) || \result.equals(Mark.WW);
        ensures current == 0 ==> \result.equals(Mark.BB);
        ensures current != 0 ==> \result.equals(Mark.WW);
        pure
    */
    public Mark getMark() {
        Mark mark;
        if (current == 0) {
            mark = Mark.BB;
        } else {
            mark = Mark.WW;
        }
        return mark;
    }


    /**
     * Returns the game state (board and turn).
     *
     * @return game state
     */
    /*@
        ensures \result == this.board + "\nCurrent player: " + getTurn();
        pure
    */
    public String toString() {
        return this.board + "\nCurrent player: " + getTurn();
    }


    /**
     * Returns the current board of the game.
     *
     * @return the current board
     */
    /*@
        ensures \result == this.board;
        pure
    */
    public Board getBoard() {
        return this.board;
    }


    /**
     * Returns the integer representing the current player's turn.
     *
     * @return the integer representing the current player's turn.
     */
    /*@
        ensures \result == this.current;
        ensures \result == 0 || \result == 1;
        pure
    */
    public int getCurrent() {
        return current;
    }

    /**
     * Changes the value of current.
     *
     * @param current the integer representing the current player's turn
     */
    /*@
        requires current > 0;
        ensures getCurrent() == current;
    */
    public void setCurrent(int current) {
        this.current = current;
    }


}
