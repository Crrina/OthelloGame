package ss.othello.ui;


import ss.othello.exceptions.NoMoveEntered;
import ss.othello.game.model.Move;
import ss.othello.game.model.OthelloMove;
import ss.othello.networking.ClassFactory;
import ss.othello.networking.Factory;
import ss.othello.networking.client.Client;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.util.ArrayList;
import java.util.InputMismatchException;
import java.util.List;
import java.util.Random;

/**
 * The Main application for Users to use.
 * This application creates clients to connect to the server,
 * according to the hostname and port number entered.
 * It takes the user input and sends it to the Client.
 */
public class OthelloTui {


    private Factory factory = new ClassFactory();
    private Client client;
    private BufferedReader reader;

    private List<String> queue = new ArrayList<>();

    /**
     * The main method which users use to operate the Tui.
     *
     * @param args command line arguments
     */
    public static void main(String[] args) {
        OthelloTui tui = new OthelloTui();
        tui.handleConnection();
        if (tui.handleLogIn()) {
            tui.getUserCommands();
        } else {
            tui.getClient().close();
        }
    }

    /**
     * Returns the client.
     *
     * @return the client
     */
    private Client getClient() {
        return client;
    }


    /**
     * Handles the connection made by the client to the server.
     * The user will be asked for a server address and a port number.
     */
    private void handleConnection() {

        reader = new BufferedReader(new InputStreamReader(System.in));


        client = factory.makeClient();


        while (true) {

            try {
                System.out.println("Input the server address:");
                String server = reader.readLine();

                System.out.println("Input the port number the server runs on:");
                int port = Integer.parseInt(reader.readLine());


                if (!client.connect(InetAddress.getByName(server), port)) {
                    System.err.println("Could not connect!");
                } else {
                    break;
                }

            } catch (IOException e) {
                System.err.println("Could not connect");
            } catch (NumberFormatException e) {
                System.err.println("Enter a number!");
            } catch (IllegalArgumentException e) {
                System.err.println("Invalid port number!");
            }
        }

    }

    /**
     * Handles logging in to the server.
     * It asks the user to enter a name that is going
     * to get sent to the server.
     *
     * @return true if login was successful, false otherwise
     */
    private boolean handleLogIn() {
        try {

            if (!client.sendHello()) {
                System.err.println("Lost connection!");
                return false;
            }

            // waits for hello from the server
            synchronized (client) {
                client.wait();
            }


            System.out.println("Please give a username: ");
            String userName = checkUsername();
            client.sendUsername(userName);
            // waits for server response
            synchronized (client) {
                client.wait();
            }

            // if the client gets Logged in, it will not enter the while loop.
            while (!client.getClientLoggedIn()) {
                System.err.println("Username taken! Input another username: ");
                userName = checkUsername();
                client.sendUsername(userName);
                // waits server response
                synchronized (client) {
                    client.wait();
                }
            }
            return true;
        } catch (IOException e) {
            System.err.println("IO exception");
            return false;
        } catch (InterruptedException e) {
            System.err.println("The thread was interrupted!");
            return false;
        }

    }

    /**
     * Checks that a username does not contain the protocol separator.
     *
     * @return The username entered by the user
     * @throws IOException Error in IO
     */
    private String checkUsername() throws IOException {
        while (true) {
            String line = reader.readLine();
            if (line.contains("~")) {
                System.err.println("A username cannot contain '~'. Please try again.");
            } else {
                return line;
            }
        }
    }


    /**
     * Receives commands from the user console.
     * It runs in a while loop and if QUIT is inputted
     * by the user it stops the application.
     */
    private void getUserCommands() {
        String line;
        try {
            // waits in a while loop for user input
            while ((line = reader.readLine()) != null) {
                if (line.equalsIgnoreCase("quit")) {
                    break;
                }
                handleUserInput(line);
            }
        } catch (IOException e) {
            System.err.println("An IO Exception has occurred!");
        } finally {
            client.close();
        }
    }


    /**
     * Handles the commands entered by users
     * via System.in. Depending on the user
     * input it will call methods from the client
     * class.
     *
     * @param input The user input
     */
    private void handleUserInput(String input) {

        String[] line = input.toUpperCase().split("\\s+");
        switch (line[0]) {
            case "LIST":
                if (client.getClientLoggedIn()) {
                    client.requestList();
                }
                break;
            case "QUEUE":
                if (!client.getClientPlays()) {
                    if (queue.contains(client.getUserName())) {
                        System.out.println("You have been removed from the queue");
                        queue.remove(client.getUserName());
                    } else {
                        System.out.println("You have been placed in the queue");
                        queue.add(client.getUserName());
                    }
                    if (client.getClientLoggedIn()) {
                        client.requestQueue();
                    }
                } else {
                    System.err.println("Invalid command!");
                }
                break;
            case "MOVE":
                if (client.getClientLoggedIn() && client.getClientPlays() && client.getHasTurn()) {
                    try {
                        if (line.length != 2) {
                            throw new NoMoveEntered("You have to enter the field");
                        }
                        int field = Integer.parseInt(line[1]);
                        if (client.getGame().isValidMove(new OthelloMove(client.getGame().getMark(),
                                field, client.getGame().getBoard()))) {
                            client.setTurn(false);
                            client.sendMove(field);
                        } else {
                            System.err.println("This is not a valid move!");
                        }
                    } catch (NoMoveEntered e) {
                        System.err.println("Enter the move correctly!");
                    } catch (NumberFormatException | InputMismatchException e) {
                        System.err.println("You need to enter a number!");
                    }
                } else {
                    System.err.println("Invalid command!");
                }
                break;
            case "HUMAN":
                queue.remove(client.getUserName());
                if (client.getClientPlays() && client.getHasTurn()) {
                    System.out.println(client.getGame() +
                            " with mark " + client.getGame().getMark());
                    System.out.println("You go first!");
                    client.setClientStartedGame(true);
                    System.out.println("To get a hint enter 'HINT'");
                    System.out.println("Make a move by entering " +
                            "'Move [number]' (without the [] brackets) ");
                    System.out.println("To find the move number, " +
                            "look at the reference board on the right:");
                } else if (client.getClientPlays()) {
                    System.out.println(client.getGame() +
                            " with mark " + client.getGame().getMark());
                    System.out.println("Your opponent goes first!");
                    client.setClientStartedGame(true);
                    // in case the other client sent a move, the client thread will wait
                    // until the user gives input, this just notifies it.
                    synchronized (client) {
                        client.notifyAll();
                    }
                } else {
                    System.err.println("Invalid command!");
                }
                break;
            case "AI":
                queue.remove(client.getUserName());
                if (client.getClientPlays()) {
                    client.setAi(true);
                    System.out.println("Enter 'NaiveAi' to play as a naive ai\n" +
                            "Enter 'SmartAi' to play as a smart ai");
                } else {
                    System.err.println("Invalid command!");
                }
                break;
            case "HINT":
                if (client.getClientPlays() && client.hasClientStartedGame()
                        && !client.isAi() && client.getHasTurn()) {
                    List<Integer> moves = new ArrayList<>();
                    for (Move move : client.getGame().getValidMoves()) {
                        moves.add(move.getField());
                    }
                    System.out.println(moves.get(new Random().nextInt(moves.size()))
                            + " is a possible move");
                } else {
                    System.err.println("Invalid command!");
                }
                break;
            case "NAIVEAI":
                checkAi("naive");
                break;
            case "SMARTAI":
                checkAi("smart");
                break;
            case "HELP":
                client.showOptions();
                break;
            default:
                System.err.println("Invalid command!");
                break;

        }
    }

    /**
     * Checks the type of Strategy a user wants to use for a
     * computer player on the network, only if they choose to
     * play as a computer player.
     *
     * @param ai The type of AI, "smart" or "naive".
     */
    private void checkAi(String ai) {
        if (client.getClientPlays() && client.isAi()) {
            if (ai.equals("smart")) {
                client.setSmartAi(true);
            } else if (ai.equals("naive")) {
                client.setNaiveAi(true);
            }
            if (client.getHasTurn()) {
                System.out.println("You go first!");
                client.setClientStartedGame(true);
                client.setAllowed(true);
            } else {
                System.out.println("Your opponent goes first!");
                client.setClientStartedGame(true);
                client.setAllowed(true);
                synchronized (client) {
                    client.notifyAll();
                }
            }
            client.startAi();
        } else if (client.getClientPlays()) {
            System.out.println("Enter 'Ai' to play as an ai\n" +
                    "Enter 'Human' to play as a smart ai");
        } else {
            System.err.println("Invalid command!");
        }
    }


}








