package ss.othello.game.ai;

import ss.othello.game.model.AbstractPlayer;
import ss.othello.game.model.Game;
import ss.othello.game.model.Mark;
import ss.othello.game.model.Move;

/**
 * This class models the player which is controlled by AI strategies.
 */
public class ComputerPlayer extends AbstractPlayer {
    /*@
       private  invariant mark.equals(Mark.BB) || mark.equals(Mark.WW);
    */

    private Mark mark;
    private Strategy strategy;

    /**
     * Constructor for the Computer Player.
     *
     * @param mark     Mark used by the computer player
     * @param strategy Strategy used by the computer player
     */
    /*@
        requires mark != null && strategy != null;

    */
    public ComputerPlayer(Mark mark, Strategy strategy) {
        super(strategy.getName() + "-" + mark);
        this.mark = mark;
        this.strategy = strategy;
    }

    /**
     * Determines the next move, if the player still has valid moves.
     *
     * @param game the current game
     * @return the move based on the strategy used
     */
    /*@
        requires game != null;
        ensures !game.isGameover() ==> game.getValidMoves().contains(\result);
    */
    @Override
    public Move determineMove(Game game) {
        Move move = strategy.determineMove(game);
        if (move == null) {
            System.out.println("There are no moves for the player " +
                    getName() + " with mark " + mark + " !");
            return null;
        }
        return move;
    }


}
