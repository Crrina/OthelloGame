package ss.othello.test;


import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import ss.othello.game.ai.NaiveStrategy;
import ss.othello.game.ai.Strategy;
import ss.othello.game.localTUI.HumanPlayer;
import ss.othello.game.model.Game;
import ss.othello.game.model.Move;
import ss.othello.game.model.OthelloGame;
import ss.othello.game.model.Player;
import ss.othello.networking.Protocol;
import ss.othello.networking.server.Server;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * This class has tests to ensure the server functions.
 */
public class ServerTest {

    private Server server;

    /**
     * The server needs to start before every test.
     */
    @BeforeEach
    void setUp() {
        server = new Server(44444);
        server.start();
    }

    /**
     * Tests if the messages are processed correctly and send back
     * by the protocol rules.
     *
     * @throws IOException error in IO
     */
    @Test
    void testProtocol() throws IOException {

        // connect to the server
        Socket socket = new Socket(InetAddress.getLocalHost(), server.getPort());
        String line;

        try (BufferedReader bufferedReader = new BufferedReader(
                new InputStreamReader(socket.getInputStream())
        );
             PrintWriter printWriter = new PrintWriter(
                     new OutputStreamWriter(socket.getOutputStream()),
                     true)) {

            List<String> users = new ArrayList<>(); // list of users we store locally

            // Send hello to the server
            printWriter.println(Protocol.sendHello("FromClient"));
            line = bufferedReader.readLine();
            assertEquals(Protocol.HELLO, line.split(Protocol.SEPARATOR)[0]);

            printWriter.println(Protocol.loginClient("Name"));
            line = bufferedReader.readLine();
            assertEquals(Protocol.LOGIN, line);
            users.add("Name"); // add user to the list after LOGIN


            printWriter.println(Protocol.LIST);
            line = bufferedReader.readLine();

            assertEquals(Protocol.forwardList(users), line);


        } finally {
            socket.close();
            server.stop();
        }

    }


    /**
     * Tests the parsing of the messages according to the protocol.
     *
     * @throws IOException error in IO
     */
    @Test
    void testMessageParsing() throws IOException {

        // connect to the server
        Socket socket = new Socket(InetAddress.getLocalHost(), server.getPort());
        // connect the second client
        Socket socket1 = new Socket(InetAddress.getLocalHost(), server.getPort());
        String line;

        try (BufferedReader bufferedReader = new BufferedReader(
                new InputStreamReader(socket.getInputStream())
        );
             PrintWriter printWriter = new PrintWriter(
                     new OutputStreamWriter(socket.getOutputStream()), true
             );
             BufferedReader reader = new BufferedReader(
                     new InputStreamReader(socket1.getInputStream())
             );
             PrintWriter writer = new PrintWriter(
                     new OutputStreamWriter(socket1.getOutputStream()), true
             )) {


            List<String> users = new ArrayList<>(); // list of client usernames we store locally
            // Send hello to the server
            printWriter.println(Protocol.sendHello("FromClient"));
            line = bufferedReader.readLine();

            assertEquals(Protocol.HELLO, line.split(Protocol.SEPARATOR)[0]);


            printWriter.println(Protocol.loginClient("Player1"));
            line = bufferedReader.readLine();
            assertEquals(Protocol.LOGIN, line);
            users.add("Player1"); // add user to list after LOGIN


            printWriter.println(Protocol.LIST);
            line = bufferedReader.readLine();

            assertEquals(Protocol.forwardList(users), line);


            // for the second client
            writer.println(Protocol.sendHello("FromClient1"));
            line = reader.readLine();
            assertEquals(Protocol.HELLO, line.split(Protocol.SEPARATOR)[0]);


            // test login with existing username
            writer.println(Protocol.loginClient("Player1"));
            line = reader.readLine();
            assertEquals(Protocol.ALREADYLOGGEDIN, line);

            // test login with unique username
            writer.println(Protocol.loginClient("Player2"));
            line = reader.readLine();
            assertEquals(Protocol.LOGIN, line);
            users.add("Player2"); // Add username to our list of clients connected after LOGIN


            // test list command
            writer.println(Protocol.LIST);
            line = reader.readLine();
            assertEquals(Protocol.forwardList(users), line);


            printWriter.println(Protocol.QUEUE);
            Thread.sleep(100); // to ensure for this test file only, player 1 queues first
            writer.println(Protocol.QUEUE);

            // new game starts as queue size >= 2
            line = bufferedReader.readLine();
            assertEquals(Protocol.sendNewGame("Player1", "Player2"), line);

            // message send to player 2 too
            line = reader.readLine();
            assertEquals(Protocol.sendNewGame("Player1", "Player2"), line);

            // first player makes a move
            printWriter.println(Protocol.sendMove(19));
            line = bufferedReader.readLine();
            assertEquals(Protocol.sendMove(19), line);
            line = reader.readLine();
            assertEquals(Protocol.sendMove(19), line);

            // second player makes a move
            writer.println(Protocol.sendMove(20));
            line = reader.readLine();
            assertEquals(Protocol.sendMove(20), line);
            line = bufferedReader.readLine();
            assertEquals(Protocol.sendMove(20), line);

            // first player will now send an invalid move
            printWriter.println(Protocol.sendMove(100));
            // the server should respond with error and kick him
            line = bufferedReader.readLine();
            assertEquals(Protocol.ERROR, line);
            // the client is kicked so the second client should get GameOver disconnect

            line = reader.readLine();
            assertEquals(Protocol.gameOverDisconnect("Player2"), line);


        } catch (InterruptedException e) {
            System.err.println(e.getMessage());
        } finally {
            socket.close();
            socket1.close();
            server.stop();
        }


    }


    /**
     * Tests 2 clients playing 3 games on the server.
     *
     * @throws IOException IO error
     */
    @Test
    public void testPlayingGame() throws IOException {


        // connect to the server
        Socket socket = new Socket(InetAddress.getLocalHost(), server.getPort());
        // connect the second client
        Socket socket1 = new Socket(InetAddress.getLocalHost(), server.getPort());
        String line;

        try (BufferedReader bufferedReader = new BufferedReader(
                new InputStreamReader(socket.getInputStream())
        );
             PrintWriter printWriter = new PrintWriter(
                     new OutputStreamWriter(socket.getOutputStream()), true
             );
             BufferedReader reader = new BufferedReader(
                     new InputStreamReader(socket1.getInputStream())
             );
             PrintWriter writer = new PrintWriter(
                     new OutputStreamWriter(socket1.getOutputStream()), true)
        ) {


            List<String> users = new ArrayList<>(); // list of usernames we store locally

            // Send hello to the server
            printWriter.println(Protocol.sendHello("FromClient"));
            line = bufferedReader.readLine();

            assertEquals(Protocol.HELLO, line.split(Protocol.SEPARATOR)[0]);


            // login user 1
            printWriter.println(Protocol.loginClient("User1"));
            line = bufferedReader.readLine();
            assertEquals(Protocol.LOGIN, line);
            users.add("User1"); // add to list when login successful


            printWriter.println(Protocol.LIST);
            line = bufferedReader.readLine();
            assertEquals(Protocol.forwardList(users), line);


            // for the second client
            writer.println(Protocol.sendHello("FromClient1"));
            line = reader.readLine();

            assertEquals(Protocol.HELLO, line.split(Protocol.SEPARATOR)[0]);


            writer.println(Protocol.loginClient("User2"));
            line = reader.readLine();
            assertEquals(Protocol.LOGIN, line);
            users.add("User2"); // add to list when login successful


            writer.println(Protocol.LIST);
            line = reader.readLine();
            assertEquals(Protocol.forwardList(users), line);


            // play 3 games
            int counter = 0;
            while (counter < 3) {

                printWriter.println(Protocol.QUEUE);
                Thread.sleep(500);
                writer.println(Protocol.QUEUE);

                line = bufferedReader.readLine();
                assertEquals(Protocol.sendNewGame("User1", "User2"), line);

                line = reader.readLine();
                assertEquals(Protocol.sendNewGame("User1", "User2"), line);

                // players start making random moves
                // using the naive ai
                Strategy strategy = new NaiveStrategy();
                Player player1 = new HumanPlayer("User1");
                Player player2 = new HumanPlayer("User2");
                Game game = new OthelloGame(player1, player2);

                while (!game.isGameover()) {
                    Move move;
                    PrintWriter toWrite;
                    if (game.getTurn().equals(player1)) {
                        toWrite = printWriter;
                    } else {
                        toWrite = writer;
                    }

                    if (!game.getValidMoves().isEmpty()) {
                        move = strategy.determineMove(game);
                        toWrite.println(Protocol.sendMove(move.getField()));
                        line = bufferedReader.readLine();
                        // verify if the move the server sends back is the same
                        // as the move the client sent
                        assertEquals(Protocol.sendMove(move.getField()), line);
                        line = reader.readLine();
                        assertEquals(Protocol.sendMove(move.getField()), line);
                        game.doMove(move);

                    } else {
                        toWrite.println(Protocol.sendMove(64));
                        line = bufferedReader.readLine();
                        assertEquals(Protocol.sendMove(64), line);
                        line = reader.readLine();
                        assertEquals(Protocol.sendMove(64), line);

                        // set the turn
                        int current = game.getCurrent() == 0 ? 1 : 0;
                        game.setCurrent(current);
                    }
                }

                if (game.isGameover()) {
                    if (game.getWinner() != null && game.getWinner().equals(player1)) {
                        line = bufferedReader.readLine();
                        assertEquals(Protocol.gameOverVictory("User1"), line);
                        line = reader.readLine();
                        assertEquals(Protocol.gameOverVictory("User1"), line);
                    } else if (game.getWinner() != null && game.getWinner().equals(player2)) {
                        line = bufferedReader.readLine();
                        assertEquals(Protocol.gameOverVictory("User2"), line);
                        line = reader.readLine();
                        assertEquals(Protocol.gameOverVictory("User2"), line);
                    } else {
                        line = bufferedReader.readLine();
                        assertEquals(Protocol.gameOverDraw(), line);
                        line = reader.readLine();
                        assertEquals(Protocol.gameOverDraw(), line);
                    }
                }

                counter++;
            }


        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        } finally {
            socket.close();
            socket1.close();
            server.stop();
        }

    }


}
