package ss.othello.game.ai;

import ss.othello.game.model.*;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

/**
 * The strategy used by a computer player which checks the
 * move with the highest score.
 * The computer player then plays this move.
 */
public class SmartStrategy implements Strategy {

    private String smartStrategy = "Smart";

    /**
     * Returns the name of the strategy.
     *
     * @return the name of the strategy.
     */
    /*@
        ensures \result == smartStrategy;
    */
    @Override
    public String getName() {
        return smartStrategy;
    }

    /**
     * Determines the move by checking which move gives the most points.
     *
     * @param game the current game
     * @return move which gives the most points, null if there are no valid moves
     */
    /*@
        ensures game.getValidMoves().isEmpty() ==> \result == null;
        ensures (\forall Move move; game.getValidMoves().contains(move) && !move.equals(\result);
        flipCount(move) < flipCount(\result));
    */
    @Override
    public Move determineMove(Game game) {
        List<Move> moves = new ArrayList<>();
        Board board =  game.getBoard();
        Mark mark = game.getMark();
        int score = 0;
        for (Move validMove : game.getValidMoves()) {
            if (validMove.getMark() == mark) {
                int curr = flipCount(new OthelloMove(mark, validMove.getField(), board));
                if (curr > score) {
                    moves.clear();
                    moves.add(new OthelloMove(mark, validMove.getField(), board));
                    score = curr;
                } else if (curr == score) {
                    moves.add(new OthelloMove(mark, validMove.getField(), board));
                }
            }
        }
        if (moves.isEmpty()) {
            return null;
        } else {
            return moves.get(new Random().nextInt(moves.size()));
        }
    }

    /**
     * This method checks how many marks will be flipped on the board, given a move.
     *
     * @param move the Move to check the number of marks flipped
     * @return the number of marks of the opponent which will be flipped
     */
    /*@
        requires move != null;
        ensures (\forall Move valid; move.getBoard().calculateValidMoves
        (move.getMark()).containsKey(move.getField()); \result > 0);
        pure
    */
    private int flipCount(Move move) {
        /*
         this method is similar to flipOpponent in Move,
         but it counts the pieces to flip instead of actually flipping
        */
        int toFlip;
        int counter = 0;
        int field = move.getField();
        Board board =  move.getBoard();
        Mark mark = move.getMark();
        int row = field / board.getDim();
        int col = field % board.getDim();
        int rowFlip;
        int colFlip;
        int upperLimit = board.calculateValidMoves(mark).get(field).size();
        List<Integer> list = board.calculateValidMoves(mark).get(field);
        for (int i = 0; i < upperLimit; i++) {
            toFlip = list.get(i);
            rowFlip = toFlip / board.getDim();
            colFlip = toFlip % board.getDim();
            if (row == rowFlip) {
                if (toFlip > field) {
                    for (int j = field; j < toFlip; j++) {
                        counter++;
                    }
                } else {
                    for (int j = field; j > toFlip; j--) {
                        counter++;
                    }
                }
            }
            if (col == colFlip) {
                if (toFlip > field) {
                    for (int j = field; j < toFlip; j += 8) {
                        counter++;
                    }
                } else {
                    for (int j = field; j > toFlip; j -= 8) {
                        counter++;
                    }
                }
            }
            if (row < rowFlip && col < colFlip) {
                for (int j = field + 9; j < toFlip; j += 9) {
                    counter++;
                }
            } else if (row > rowFlip && col > colFlip) {
                for (int j = field - 9; j > toFlip; j -= 9) {
                    counter++;
                }
            } else if (row > rowFlip && col < colFlip) {
                for (int j = field - 7; j > toFlip; j -= 7) {
                    counter++;
                }
            } else if (row < rowFlip && col > colFlip) {
                for (int j = field + 7; j < toFlip; j += 7) {
                    counter++;
                }
            }
        }
        return counter;
    }
}
