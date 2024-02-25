package ss.othello.game.model;

/**
 * The abstract class which represents what shared methods different players do.
 * All players have a common getName and toString method but have different
 * ways to determine a move.
 */
public abstract class AbstractPlayer implements Player {

    //@private invariant name != null;

    private final String name;

    /**
     * Creates a new Player object.
     *
     * @param name name of the player
     */
    /*@ requires name != null;
        ensures getName() == name;
    @*/
    public AbstractPlayer(String name) {
        this.name = name;
    }

    /**
     * Returns the name of the player.
     *
     * @return the name of the player
     */
    /*@
        ensures \result == this.name;
        pure
    */
    public String getName() {
        return name;
    }

    /**
     * Determines the next move if the game still has available moves.
     *
     * @param game the current game
     * @return the player's choice
     */
    /*@
        requires !game.isGameover();
        ensures game.isValidMove(\result);
    */
    public abstract Move determineMove(Game game);

    /**
     * Returns a representation of a player, i.e., their name.
     *
     * @return the String representation of this object
     */
    /*@
        ensures \result.equals("Player " + getName());
    */
    @Override
    public String toString() {
        return "Player " + name;
    }


}

