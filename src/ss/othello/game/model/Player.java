package ss.othello.game.model;


/**
 * The interface which models the player's methods.
 * A player has a name.
 */
public interface Player {


    /**
     * Returns the name of the player.
     *
     * @return the name of the player
     */
    /*@
        ensures \result != null;
        pure
    */
    String getName();


    /**
     * Returns a representation of a player, i.e., their name.
     *
     * @return the String representation of this object
     */

    String toString();



}
