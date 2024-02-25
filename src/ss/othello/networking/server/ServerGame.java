package ss.othello.networking.server;

import ss.othello.game.localTUI.HumanPlayer;
import ss.othello.game.model.*;
import ss.othello.networking.Protocol;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;

/**
 * The class ServerGame that is created when a new game is created.
 * It is responsible for creating a new game for 2 client
 * handlers. It sends a new game message when the game starts. When the clients
 * send moves, the ServerGame checks the move, updates the game status and sends the move
 * back. It handles the game over by sending the winner at the end of the game.
 */
public class ServerGame {


    private ClientHandler client1;
    private ClientHandler client2;

    private Server server;

    private Game game;

    private BufferedWriter writer1;
    private BufferedWriter writer2;

    private String player1;
    private String player2;


    /**
     * Constructor for the OthelloGame played on the network, hosted by the server.
     *
     * @param client1 Handler for player 1
     * @param client2 Handler for player 2
     * @param server  Server which hosts the game
     */
    public ServerGame(ClientHandler client1, ClientHandler client2, Server server) {
        this.server = server;
        this.client1 = client1;
        this.client2 = client2;
        this.player1 = client1.getName();
        this.player2 = client2.getName();
        this.game = new OthelloGame(new HumanPlayer(player1), new HumanPlayer(player2));
        try {
            this.writer1 = new BufferedWriter(new OutputStreamWriter(
                    this.client1.getSocket().getOutputStream())
            );
            this.writer2 = new BufferedWriter(new OutputStreamWriter(
                    this.client2.getSocket().getOutputStream())
            );
        } catch (IOException e) {
            System.err.println("An IO exception happened!");
        }
    }


    /**
     * Used to start a new game. When a new game is created
     * this method calls the changeGame() from the ClientHandler class
     * that sends the NEWGAME~ message.
     *
     * @return true id the game was started successfully, otherwise false.
     */
    public boolean startGame() {
        client1.changeGame(true, player1, player2, this);
        client2.changeGame(true, player1, player2, this);
        return true;
    }


    /**
     * This method is used for making a move in the game.
     * It checks if the move is valid and if the user has the turn
     * before making the move, updating the game status and sending the
     * move back.
     * If index 64 is sent it will pass the turn to the next player.
     *
     * @param name  of the client that sent the move.
     * @param index of the move, where it should be placed on the board.
     */
    public void makeMove(String name, int index) {
        synchronized (this.game) {
            if (game.getTurn().getName().equals(name)) {
                if (!game.isGameover()) {
                    Mark mark = game.getMark();
                    Move move = new OthelloMove(mark, index, game.getBoard());
                    if (game.isValidMove(move)) {
                        game.doMove(move);
                    } else if (index == 64 && game.getValidMoves().size() == 0) {
                        // check if the client indeed has no moves
                        int current = game.getCurrent() == 0 ? 1 : 0;
                        game.setCurrent(current);
                    } else {
                        if (client1.getName().equals(name)) {
                            client1.handleError();
                        } else {
                            client2.handleError();
                        }
                    }
                    if (!checkDisconnects()) {
                        sendMove(index);
                    }
                    if (game.isGameover()) {
                        if (!checkDisconnects()) {
                            handleGameOver();
                        }
                    }
                }
            } else {
                stopGame();
            }
        }
    }


    /**
     * Checks for disconnects during the game. If one player
     * leaves the game, this method informs the player of the disconnect
     * by sending victory due to opponent disconnecting. It will stop the game
     * at the end if a disconnect has occurred.
     *
     * @return true if a player disconnected from the server, otherwise false.
     */
    public synchronized boolean checkDisconnects() {
        try {
            if (!client1.hasConnection()) {
                writer2.write(Protocol.gameOverDisconnect(player2));
                writer2.newLine();
                writer2.flush();
                stopGame();
                return true;
            }
            if (!client2.hasConnection()) {
                writer1.write(Protocol.gameOverDisconnect(player1));
                writer1.newLine();
                writer1.flush();
                stopGame();
                return true;
            }
        } catch (IOException e) {
            System.err.println("An IO exception happened!");
        }
        return false;
    }


    /**
     * Sends the move made by the client back.
     * This method is called only if the makeMove()
     * method checked if the move is valid, the game is not
     * over and no one disconnected.
     *
     * @param move to be sent back to the client.
     */
    private void sendMove(int move) {
        try {
            writer1.write(Protocol.sendMove(move));
            writer2.write(Protocol.sendMove(move));
            writer1.newLine();
            writer2.newLine();
            writer1.flush();
            writer2.flush();
        } catch (IOException e) {
            System.out.println("Error happened");
        }
    }


    /**
     * Handles the game over. It is called
     * when the game has ended. It calls sendVictory()
     * that sends the message that indicates the winner of the game
     * or if it was draw.
     *
     * @return true if the winner/gameover status was successfully
     * sent, else return false.
     */
    private boolean handleGameOver() {
        if (game.getBoard().hasWinner()) {
            stopGame();
            Player player = game.getWinner();
            if (player.getName().equals(player1)) {
                sendVictory(player1);
            } else if (player.getName().equals(player2)) {
                sendVictory(player2);
            }
            return true;
        } else {
            try {
                stopGame();
                writer1.write(Protocol.gameOverDraw());
                writer2.write(Protocol.gameOverDraw());
                writer1.newLine();
                writer2.newLine();
                writer1.flush();
                writer2.flush();
                return true;
            } catch (IOException e) {
                System.err.println("An IO exception has occurred!");
                return false;
            }
        }
    }


    /**
     * Stops the game when it is over.
     * Calls the method changeGame() from ClientHandler, that checks
     * that the names are empty, thus the client handler is removed from the
     * game.
     */
    public void stopGame() {
        client1.changeGame(false, "", "", this);
        client2.changeGame(false, "", "", this);
        server.getServerGames().remove(this);
    }


    /**
     * Sends victory, when the game has ended.
     * It will send the message GAMEOVER~VICTORY~name to both
     * clients.
     *
     * @param name of the client who won the game.
     */
    private void sendVictory(String name) {
        try {
            writer1.write(Protocol.gameOverVictory(name));
            writer2.write(Protocol.gameOverVictory(name));
            writer1.newLine();
            writer2.newLine();
            writer1.flush();
            writer2.flush();
        } catch (IOException e) {
            System.err.println("An IO exception has occurred!");
        }
    }


}
