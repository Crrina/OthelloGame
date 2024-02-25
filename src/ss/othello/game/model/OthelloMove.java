package ss.othello.game.model;


import java.util.List;

/**
 * Uses the Move interface to represent a move
 * in Othello.
 * A move has a mark, placed on an index in a board.
 * Placing a mark and capturing opponent pieces also flips the colour
 * of the mark.
 */
public class OthelloMove implements Move {


    //@private invariant field >= 0 && field < 64;

    private Mark mark;

    private int field;

    private Board board;

    /**
     * Constructor for the OthelloMove.
     *
     * @param mark  mark to place on board
     * @param field index of board place at
     * @param board board to place marker on
     */
    /*@
        requires mark.equals(Mark.BB) || mark.equals(Mark.WW);
        requires board != null;
        requires field >= 0 && field <= board.getDim();
        ensures this.mark == mark && this.board == board && this.field == field;
    */
    public OthelloMove(Mark mark, int field, Board board) {
        this.mark = mark;
        this.field = field;
        this.board = board;
    }

    /**
     * Returns the mark of the move.
     *
     * @return mark, belonging to this move.
     */
    /*@
        ensures \result == this.mark;
        pure
    */
    public Mark getMark() {
        return mark;
    }

    /**
     * Returns the field of the move.
     *
     * @return field, the number that represents the index
     * of this move on the board.
     */
    /*@
        ensures \result == this.field;
        pure
    */
    public int getField() {
        return field;
    }

    /**
     * Makes the move in the Othello game.
     * It flips the opponents pieces and sets
     * them to the current player mark.
     */
    //@ensures board.getField(field) == mark;
    public void move() {
        flipOpponent();
        board.setField(field, mark);
    }

    /**
     * Returns the board of the game
     *
     * @return board of the game
     */
    /*@
        ensures \result == this.board;
    */
    public Board getBoard() {
        return board;
    }

    /**
     * Flips the marks of the opponent pieces.
     * It starts flipping beginning with the current
     * move index, until it encounters another mark with
     * the same color.
     */
    /*@
        ensures (\forall int i, j; board.isField(i); board.checkRow(i, j, mark).size() > 0
        ==> board.getField(j) == mark);
          ensures (\forall int i, j; board.isField(i); board.checkColumn(i, j, mark).size() > 0 ==>
           board.getField(j) == mark);
          ensures (\forall int i, j; board.isField(i);
          board.checkDiagonal(i, j, mark).size() > 0 ==> board.getField(j) == mark);
          pure
    */
    private void flipOpponent() {
        int row = field / board.getDim();
        int col = field % board.getDim();
        int rowFlip;
        int colFlip;
        int upperLimit = board.calculateValidMoves(mark).get(field).size();
        //list with all valid moves
        List<Integer> list = board.calculateValidMoves(mark).get(field);
        for (int i = 0; i < upperLimit; i++) {
            //this returns the element from the same color list , until where to flip
            int toFlip = list.get(i);
            rowFlip = toFlip / board.getDim();
            colFlip = toFlip % board.getDim();
            if (row == rowFlip) {
                if (toFlip > field) {
                    for (int j = field; j < toFlip; j++) {
                        board.setField(j, mark);
                    }
                } else {
                    for (int j = field; j > toFlip; j--) {
                        board.setField(j, mark);
                    }
                }
            }
            if (col == colFlip) {
                if (toFlip > field) {
                    for (int j = field; j < toFlip; j += 8) {
                        board.setField(j, mark);
                    }
                } else {
                    for (int j = field; j > toFlip; j -= 8) {
                        board.setField(j, mark);
                    }
                }
            }
            if (row < rowFlip && col < colFlip) {
                for (int j = field + 9; j < toFlip; j += 9) {
                    board.setField(j, mark);
                }
            } else if (row > rowFlip && col > colFlip) {
                for (int j = field - 9; j > toFlip; j -= 9) {
                    board.setField(j, mark);
                }
            } else if (row > rowFlip && col < colFlip) {
                for (int j = field - 7; j > toFlip; j -= 7) {
                    board.setField(j, mark);
                }
            } else if (row < rowFlip && col > colFlip) {
                for (int j = field + 7; j < toFlip; j += 7) {
                    board.setField(j, mark);
                }
            }
        }
    }

}
