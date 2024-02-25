package ss.othello.exceptions;


/**
 * Class for the exception InvalidPortNumber.
 * This exception is thrown when the server
 * (ServerStart) class is started with an invalid
 * port number (bigger than 65535 and smaller than 0).
 */
public class InvalidPortNumber extends Exception {


    /**
     * Constructs the exception.
     *
     * @param name the message of the exception
     */
    public InvalidPortNumber(String name) {
        super(name);
    }

}
