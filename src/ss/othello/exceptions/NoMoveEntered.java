package ss.othello.exceptions;


/**
 * Class for the exception NoMoveEntered.
 * This exception is thrown when the user plays
 * as a Human Player and does not input the move number,
 * only inputs "MOVE".
 */
public class NoMoveEntered extends Exception {


    /**
     * Constructs the exception.
     *
     * @param text the message of the exception
     */
    public NoMoveEntered(String text) {
        super(text);
    }

}
