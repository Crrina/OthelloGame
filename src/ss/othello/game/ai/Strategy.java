package ss.othello.game.ai;


import ss.othello.game.model.Game;
import ss.othello.game.model.Move;

/**
 * Interface which models the strategy that Computer Players use.
 */
public interface Strategy {


    /**
     * Returns the name of the strategy.
     *
     * @return the name of the strategy.
     */
    /*@
        ensures \result != null;
    */
    String getName();


    /**
     * Determines a move according to the strategy modelled.
     *
     * @param game the current game
     * @return a next legal move
     */
    /*@
        requires game != null;
    */
    Move determineMove(Game game);


}
