package ss.othello.game.localTUI;


import ss.othello.game.model.*;

import java.util.InputMismatchException;
import java.util.Scanner;

/**
 * This class represents a human player.
 * Human players enter their moves using keyboard input.
 */
public class HumanPlayer extends AbstractPlayer {

    /**
     * Creates a new Player object.
     *
     * @param name name of the player
     */
    public HumanPlayer(String name) {
        super(name);
    }

    /**
     * Determines the next move, if the game still has available moves.
     *
     * @param game the current game
     * @return the player's choice
     */
    /*@
        requires game != null;
        ensures game.getValidMoves().isEmpty() ==> \result == null;
    */
    @Override
    public Move determineMove(Game game) {
        Scanner scanner = new Scanner(System.in);
        Mark mark = game.getMark();
        Move move = null;
        while (true) {
            try {
                if (game.getValidMoves().isEmpty()) {
                    System.out.println("There are no moves for the player " +
                            getName() + " with mark " + mark + " !");
                    break;
                }
                System.out.println("Type in the index of the board. " +
                        "Use the reference board to find the index.");
                System.out.println(getName() + " with mark " + mark + " choose a move:");
                int field = scanner.nextInt();
                move = new OthelloMove(mark, field, game.getBoard());
                if (game.isValidMove(move)) {
                    break;
                } else {
                    System.err.println("This is not a valid move !");
                }


            } catch (NumberFormatException | InputMismatchException e) {
                System.err.println("You have to enter a number!");
                scanner.nextLine();

            }

        }
        return move;

    }

}