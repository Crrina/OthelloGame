package ss.othello.networking.client;

import ss.othello.game.ai.NaiveStrategy;
import ss.othello.game.ai.SmartStrategy;
import ss.othello.game.ai.Strategy;
import ss.othello.game.localTUI.HumanPlayer;
import ss.othello.game.model.Game;
import ss.othello.game.model.Move;
import ss.othello.game.model.OthelloGame;
import ss.othello.game.model.OthelloMove;
import ss.othello.networking.Protocol;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;
import java.net.SocketException;
import java.util.InputMismatchException;

/**
 * The class Client that implements the ChatClient and Runnable
 * interface. The Client class is responsible for starting the client,
 * attempting to connect to the server, sending valid commands to the
 * server and playing games of Othello on the server.
 */
public class Client implements ChatClient, Runnable {


    /**
     * The name that is sent with HELLO~.
     */
    private static final String CLIENT_NAME = "Othello Client";
    private Socket socket;
    private Thread thread;
    private BufferedWriter bufferedWriter;
    private String userName;
    private Game game;
    private String opponentName;
    private boolean clientStartedGame = false;
    private boolean allowed = false;
    private boolean clientLoggedIn = false;
    private boolean clientPlays = false;
    private boolean hasTurn = false;
    private boolean naiveAi = false;
    private boolean smartAi = false;
    private boolean ai = false;


    /**
     * Attempts to connect to the server.
     * Creates a new Thread for every new client
     * and starts it.
     *
     * @param address of the server.
     * @param port    of the server.
     * @return true if connection was successful, false otherwise
     */
    @Override
    public boolean connect(InetAddress address, int port) {
        try {
            socket = new Socket(address, port);
            bufferedWriter = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
            thread = new Thread(this);
            thread.start();
            return true;
        } catch (IOException e) {
            return false;
        }

    }


    /**
     * Returns the game.
     *
     * @return the game
     */
    public Game getGame() {
        return this.game;
    }


    /**
     * Checks if the client is logged in.
     *
     * @return true if the client is logged in, false otherwise
     */
    public boolean getClientLoggedIn() {
        return clientLoggedIn;
    }


    /**
     * Checks if a client plays.
     *
     * @return true if the client plays, false otherwise
     */
    public boolean getClientPlays() {
        return clientPlays;
    }


    /**
     * Checks if it is a client's turn.
     *
     * @return true if it is a client's turn, false otherwise
     */
    public boolean getHasTurn() {
        return hasTurn;
    }

    /**
     * Checks if the client has started the game.
     *
     * @return true if the client started the game, false otherwise
     */
    public boolean hasClientStartedGame() {
        return clientStartedGame;
    }


    /**
     * Checks if a player is a computer player.
     *
     * @return true if the player is a computer player, false otherwise
     */
    public boolean isAi() {
        return ai;
    }

    /**
     * Sets the player as AI.
     *
     * @param value true if the client choose AI, false otherwise
     */
    public void setAi(Boolean value) {
        this.ai = value;
    }

    /**
     * Starts the game if parameter is true.
     *
     * @param value true if the game is started, false otherwise
     */
    public void setClientStartedGame(Boolean value) {
        this.clientStartedGame = value;
    }

    /**
     * Sets the turn to the parameter.
     *
     * @param value true if it's the player's turn, false otherwise
     */
    public void setTurn(Boolean value) {
        this.hasTurn = value;
    }

    /**
     * Sets if the AI player is allowed to move according to the parameter.
     *
     * @param value true if the AI player can continue executing, false otherwise
     */
    public void setAllowed(Boolean value) {
        this.allowed = value;
    }

    /**
     * Sets the strategy to Naive if the parameter is true.
     *
     * @param value true if NaiveAI is chosen, false otherwise
     */
    public void setNaiveAi(Boolean value) {
        this.naiveAi = value;
    }

    /**
     * Sets the strategy to Smart if the parameter is true.
     *
     * @param value true if SmartAI is chosen, false otherwise
     */
    public void setSmartAi(Boolean value) {
        this.smartAi = value;
    }

    /**
     * Returns the client's username.
     *
     * @return the client's username
     */
    public String getUserName() {
        return this.userName;
    }


    /**
     * Prints the options (Help menu) to the client.
     */
    public void showOptions() {
        System.out.println("YOU HAVE THE FOLLOWING OPTIONS: \n" +
                "  LIST - to see the current players that are logged in\n" +
                "  QUEUE - to request to be put in a game\n" +
                "  HELP  - to get the help menu\n" +
                "  QUIT - to disconnect\n");
    }


    /**
     * Sends MOVE~64 if the player has no available moves
     * and sets the turn to false, so the opponent has turn.
     */
    private void handleNoCurrentMoves() {
        sendMove(64);
        hasTurn = false;
    }


    /**
     * Starts the AI to play, provided the player chose Smart or Naive AI.
     */
    public void startAi() {
        if (smartAi) {
            SmartStrategy smart = new SmartStrategy();
            handleAi(smart);
        }
        if (naiveAi) {
            NaiveStrategy naive = new NaiveStrategy();
            handleAi(naive);
        }
    }


    /**
     * Handles the moves made by the AI.
     * The AI will determine the valid moves and perform them.
     *
     * @param strategy The AI strategy chosen by the player
     */
    private void handleAi(Strategy strategy) {
        Move move;
        while (!game.isGameover() && clientPlays) {
            if (hasTurn && allowed) {
                move = strategy.determineMove(game);
                if (move == null) {
                    handleNoCurrentMoves();
                } else {
                    hasTurn = false;
                    allowed = true;
                    sendMove(move.getField());
                }
            }
        }
    }


    /**
     * The run method started by the Client Thread.
     * It will run in a while loop, listening to the
     * messages sent by the ClientHandler. It receives responses
     * prints them to the console accordingly and calls necessary methods
     * to handle the client game.
     */
    @Override
    public void run() {
        try {
            BufferedReader reader = new BufferedReader(
                    new InputStreamReader(socket.getInputStream())
            );
            String line = reader.readLine();
            if (line != null && line.contains(Protocol.HELLO + Protocol.SEPARATOR)) {
                String[] hello = line.split(Protocol.SEPARATOR);
                if (hello[0].equals(Protocol.HELLO) && hello.length > 1) {
                    System.out.println(Protocol.HELLO + ", welcome to " + hello[1]);
                    String extensions = "";
                    if (hello.length > 2) {
                        for (int i = 2; i < hello.length; i++) {
                            extensions += hello[i] + ", ";
                        }
                        System.out.println("The supported extensions are "
                                + extensions.substring(0, extensions.length() - 2));
                    }
                    synchronized (this) {
                        notifyAll();
                    }
                } else {
                    handleError();
                } // do this until the client is not logged in
                while (!clientLoggedIn) {
                    line = reader.readLine();
                    synchronized (this) {
                        if (line != null && line.equals(Protocol.LOGIN)) {
                            System.out.println("Login successful!");
                            clientLoggedIn = true;
                            notifyAll();
                        } else if (line != null && line.equals(Protocol.ALREADYLOGGEDIN)) {
                            notifyAll();
                        } else {
                            notifyAll();
                            handleError();
                            // some error should happen here
                        }
                    }
                }
                showOptions();
                // reads the messages from the sever after log in
                while ((line = reader.readLine()) != null) {
                    String[] message = line.split(Protocol.SEPARATOR);
                    if (message[0].equals(Protocol.LIST) && clientLoggedIn) {
                        String users = "";
                        for (int i = 1; i < line.split(Protocol.SEPARATOR).length; i++) {
                            users += line.split(Protocol.SEPARATOR)[i] + ", ";
                        }
                        System.out.println("The list of users logged in are: " +
                                users.substring(0, users.length() - 2));
                    }
                    if (!clientPlays && clientLoggedIn && message[0].equals(Protocol.NEWGAME)
                            && message.length == 3) {
                        if (message[1].equals(userName)) {
                            clientPlays = true;
                            hasTurn = true;
                            System.out.println("A new game has started!");
                            System.out.println("Player1 " + message[1]);
                            opponentName = message[2];
                            System.out.println("Player2 " + message[2]);
                            this.game = new OthelloGame(new HumanPlayer(userName),
                                    new HumanPlayer(opponentName));
                            System.out.println("Enter 'HUMAN' to play as a human");
                            System.out.println("Enter 'AI' to play as an ai");

                        } else if (message[2].equals(userName)) {
                            clientPlays = true;
                            hasTurn = false;
                            opponentName = message[1];
                            System.out.println("A new game has started!");
                            System.out.println("Player1 " + message[1]);
                            System.out.println("Player2 " + message[2]);
                            this.game = new OthelloGame(new HumanPlayer(opponentName),
                                    new HumanPlayer(userName));
                            System.out.println("Enter 'HUMAN' to play as a human");
                            System.out.println("Enter 'AI' to play as an ai");

                        } else {
                            handleError();
                        }
                    }
                    if (clientPlays && clientLoggedIn && message[0].equals(Protocol.MOVE)
                            && message.length == 2) {
                        // In case the second player did not choose if he wants to play as
                        // a human or AI, but the fst already made a move,
                        // this thread will wait until the player inputs their choice.
                        if (!hasTurn && !clientStartedGame) {
                            synchronized (this) {
                                this.wait();
                            }
                        }
                        int field = Integer.parseInt(message[1]);
                        if (field == 64) {
                            System.out.println(game.getTurn() + " has no valid moves");
                            int current = game.getCurrent() == 0 ? 1 : 0;
                            game.setCurrent(current);
                        } else {
                            System.out.println(game.getTurn() + " moved " + field);
                            game.doMove(new OthelloMove(game.getMark(), field, game.getBoard()));
                        }
                        if (game.getTurn().getName().equals(userName)) {
                            hasTurn = true;
                            allowed = false;
                        }

                        System.out.println(game + " with mark " + game.getMark());

                        if (!game.isGameover()) {
                            if (game.getValidMoves().isEmpty() && hasTurn) {
                                handleNoCurrentMoves();
                                System.out.println("You do not have any valid moves");
                            } else if (hasTurn && !ai) {
                                System.out.println("To get a hint enter 'HINT'");
                                System.out.println("Its your turn, make a move by entering " +
                                        "'Move [number]' (without the [] brackets) ");
                                System.out.println("To find the move number, " +
                                        "look at the reference board on the right:");
                            } else if (hasTurn) {
                                System.out.println("It's your turn!");
                                allowed = true;
                            } else {
                                System.out.println("It's your opponent turn!");
                            }
                        }

                    }
                    //check if there is a game over
                    if (clientPlays && clientLoggedIn && message[0].equals(Protocol.GAMEOVER)) {
                        System.out.println("The game is over!");
                        switch (message[1]) {
                            case Protocol.VICTORY:
                                System.out.println("The player " + message[2] + " has won!");
                                break;
                            case Protocol.DISCONNECT:
                                System.out.println("Player " + message[2] +
                                        " has won, due to the opponent disconnecting.");
                                break;
                            case Protocol.DRAW:
                                System.out.println("There is a draw!");
                                break;
                            default:
                                handleError();
                                break;
                        }
                        //resets the variables responsible for the game
                        clientPlays = false;
                        hasTurn = false;
                        clientStartedGame = false;
                        ai = false;
                        smartAi = false;
                        naiveAi = false;
                        allowed = false;
                        System.out.println("Enter QUEUE to play again or HELP to see the commands");
                    }
                }
            }
        } catch (NumberFormatException | InputMismatchException e) {
            System.err.println("There was an invalid message sent by the server");
            handleError();
            // Then the client handler sent an incorrect message
            // when parsing the move if it is not a number just disconnect.
        } catch (SocketException e) {
            System.out.println("The client disconnected");
        } catch (IOException e) {
            System.err.println("Can not read from the socket");
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        } finally {
            close();
        }
    }


    /**
     * Sends the username to the server (client handler).
     *
     * @param userNameLocal username to be sent
     * @return true if the username is sent successfully, false otherwise.
     */
    @Override
    public boolean sendUsername(String userNameLocal) {
        try {
            // if the client is connected to the server
            // send the userNameLocal to the server
            this.userName = userNameLocal;
            bufferedWriter.write(Protocol.loginClient(userNameLocal));
            bufferedWriter.newLine();
            bufferedWriter.flush();
            return true;
        } catch (IOException e) {
            System.err.println("Lost connection");
            close();
            return false;
        }
    }


    /**
     * Sends the HELLO message to the server according to the protocol.
     *
     * @return true if HELLO is sent properly, false otherwise
     */
    public boolean sendHello() {
        try {
            bufferedWriter.write(Protocol.sendHello(CLIENT_NAME));
            bufferedWriter.newLine();
            bufferedWriter.flush();
            return true;
        } catch (IOException e) {
            close();
            return false;
        }

    }


    /**
     * Requests the server to send a list of all connected clients.
     *
     * @return true if the request is sent successfully, false otherwise
     */
    public boolean requestList() {
        try {
            bufferedWriter.write(Protocol.LIST);
            bufferedWriter.newLine();
            bufferedWriter.flush();
            return true;
        } catch (IOException e) {
            close();
            return false;
        }
    }


    /**
     * Requests the server to add the client to the queue of clients
     * waiting for a game, or remove them from the queue if they are
     * already in the queue.
     *
     * @return true if the request is sent successfully, false otherwise
     */
    public boolean requestQueue() {
        try {
            bufferedWriter.write(Protocol.QUEUE);
            bufferedWriter.newLine();
            bufferedWriter.flush();
            return true;
        } catch (IOException e) {
            close();
            return false;
        }
    }

    /**
     * Sends the move to the client handler during the game,
     * so the server can handle the server game.
     *
     * @param move the index of the move being played
     * @return true if the move is sent successfully, false otherwise
     */
    public boolean sendMove(int move) {
        try {
            hasTurn = false;
            bufferedWriter.write(Protocol.sendMove(move));
            bufferedWriter.newLine();
            bufferedWriter.flush();
            return true;
        } catch (IOException e) {
            close();
            return false;
        }
    }


    /**
     * Sends ERROR to the client handler
     * in case it sends an invalid message.
     */
    private void handleError() {
        try {
            bufferedWriter.write(Protocol.ERROR);
            bufferedWriter.newLine();
            bufferedWriter.flush();
        } catch (IOException e) {
            System.err.println("An IO Exception has occurred!");
        }
    }


    /**
     * Closes the connection to the server
     * and finishes the execution of the program.
     */
    @Override
    public void close() {
        try {
            socket.close();
            System.exit(0);
        } catch (IOException e) {
            System.err.println("An IO exception has occurred");
        }
    }
}