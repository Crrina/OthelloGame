package ss.othello.networking;

import java.util.List;

/**
 * Protocol class with constants and methods for creating protocol messages.
 */
public final class Protocol {


    public static final String HELLO = "HELLO";
    public static final String LOGIN = "LOGIN";
    public static final String ALREADYLOGGEDIN = "ALREADYLOGGEDIN";
    public static final String LIST = "LIST";
    public static final String NEWGAME = "NEWGAME";
    public static final String MOVE = "MOVE";
    public static final String GAMEOVER = "GAMEOVER";

    public static final String QUEUE = "QUEUE";

    public static final String VICTORY = "VICTORY";

    public static final String DISCONNECT = "DISCONNECT";

    public static final String DRAW = "DRAW";

    public static final String ERROR = "ERROR";
    public static final String SEPARATOR = "~";


    /**
     * Formats the HELLO message for the handshake.
     *
     * @param name The client or server description
     * @return the formatted message according to the protocol
     */
    public static String sendHello(String name) {
        return HELLO + SEPARATOR + name;
    }


    /**
     * Formats the LOGIN message for the initialization.
     *
     * @param name The client username
     * @return the formatted message according to the protocol
     */
    public static String loginClient(String name) {
        return LOGIN + SEPARATOR + name;
    }


    /**
     * Formats the LIST message according to the protocol.
     *
     * @param userNames The list of all client usernames stored by the server
     * @return the formatted message according to the protocol
     */
    public static String forwardList(List<String> userNames) {
        String message = "";
        for (String user : userNames) {
            message = message + SEPARATOR + user;
        }
        return LIST + message;
    }

    /**
     * Formats the MOVE message according to the protocol.
     *
     * @param move The index of the move to be made
     * @return the formatted message according to the protocol
     */
    public static String sendMove(int move) {
        return Protocol.MOVE + Protocol.SEPARATOR + move;
    }

    /**
     * Formats the NEWGAME message according to the protocol.
     *
     * @param player1 Player 1 of the game (Mark BB).
     * @param player2 Player 2 of the game (Mark WW).
     * @return the formatted message according to the protocol
     */
    public static String sendNewGame(String player1, String player2) {
        return Protocol.NEWGAME + Protocol.SEPARATOR + player1 + Protocol.SEPARATOR + player2;
    }

    /**
     * Formats the DISCONNECT message according to the protocol.
     *
     * @param player winner of the game who is still connected
     * @return the formatted message according to the protocol
     */
    public static String gameOverDisconnect(String player) {
        return GAMEOVER + SEPARATOR + DISCONNECT + SEPARATOR + player;
    }

    /**
     * Formats the DISCONNECT message according to the protocol.
     *
     * @return the formatted message according to the protocol
     */
    public static String gameOverDraw() {
        return GAMEOVER + SEPARATOR + DRAW;
    }

    /**
     * Formats the VICTORY message according to the protocol.
     *
     * @param player winner of the game who is still connected
     * @return the formatted message according to the protocol
     */
    public static String gameOverVictory(String player) {
        return GAMEOVER + SEPARATOR + VICTORY + SEPARATOR + player;
    }

}
