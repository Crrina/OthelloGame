package ss.othello.game.ai;

import ss.othello.game.model.Game;
import ss.othello.game.model.Move;

import java.util.List;
import java.util.Random;

/**
 * The strategy used by Computer Players which plays a random valid move
 * (if there is a valid move).
 */
public class NaiveStrategy implements Strategy {

    private final String name = "Naive";

    /**
     * Returns the name of the strategy.
     *
     * @return the name of the strategy.
     */
    /*@
        ensures \result == this.name;
    */
    @Override
    public String getName() {
        return name;
    }

    /**
     * Returns a random move from the list of valid moves
     * for the computer player using this strategy.
     *
     * @param game the current game.
     * @return a valid move, if there are no valid moves return null.
     */
    /*@
        requires game != null;
        ensures game.getValidMoves().isEmpty() ==> \result == null;
    */
    @Override
    public Move determineMove(Game game) {
        List<Move> list = game.getValidMoves();
        if (!list.isEmpty()) {
            return list.get(new Random().nextInt(list.size()));
        }
        return null;

    }


}
