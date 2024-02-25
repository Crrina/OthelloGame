package ss.othello.networking.server;


import ss.othello.networking.Protocol;

import java.io.*;
import java.net.Socket;

import static ss.othello.networking.server.Server.SERVER_NAME;


/**
 * The ClientHandler class that implements the Runnable interface.
 * It is responsible for handling the conversation with one client.
 * It runs on a new thread, so each client has its own client handler.
 * It receives protocol messages from the client and sends back messages
 * when it is required.
 */
public class ClientHandler implements Runnable {

    private Socket socket;
    private Server server;

    private Thread thread;

    private ServerGame serverGame;

    /**
     * The username of the client(player) given at log in.
     */
    private String userName;

    private BufferedWriter bufferedWriter;

    private BufferedReader bufferedReader;


    private boolean playing;

    /**
     * Constructor for the ClientHandler. When a new ClientHandler
     * is created a new thread will be started on this client handler.
     * The writer and reader will get connected to the socket.
     *
     * @param socket the endpoint for communication between the client and the client handler.
     * @param server that creates and holds all the ClientHandlers.
     */
    public ClientHandler(Socket socket, Server server) {
        this.socket = socket;
        this.server = server;
        this.playing = false;
        try {
            bufferedWriter = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
            bufferedReader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
        } catch (IOException e) {
            System.err.println("An IO exception has occurred!");
        }
        thread = new Thread(this);
        thread.start();
    }

    /**
     * Check the status of the socket, if it's opened or closed.
     *
     * @return true if the socket is not closed, otherwise false.
     */
    public boolean hasConnection() {
        return !socket.isClosed();
    }

    /**
     * Getter for the client name handled by this client handler.
     *
     * @return the name of the client that is handled by this
     * client handler.
     */
    public String getName() {
        return userName;
    }


    /**
     * Getter for the socket.
     *
     * @return the socket this client handler uses.
     */
    public Socket getSocket() {
        return this.socket;
    }


    /**
     * The run method on which the ClientHandler runs
     * in a while loop, while listening to the messages
     * sent by the client through the socket using an InputStreamReader.
     * It checks if the messages are sent according to the Protocol
     * and makes calls to the methods from this class, the Server and
     * the ServerGame class when necessary.
     */
    @Override
    public void run() {
        try {
            String line;
            boolean receivedHello = false;
            //Need separate loops at the beginning so the client can not send Hello and
            //Login at any point.
            while (true) {
                while (!receivedHello) {
                    line = bufferedReader.readLine();
                    //if the message sent by the client
                    //does not adhere to the rules, an error is written
                    if (line != null && line.contains(Protocol.HELLO + Protocol.SEPARATOR)) {
                        String[] hello = line.split(Protocol.SEPARATOR);
                        if (hello.length > 1 && hello[0].equals(Protocol.HELLO)) {
                            receivedHello = sendHello();
                        } else {
                            //the client might have sent incorrect messages.
                            handleError();
                        }
                    } else {
                        handleError();
                    }
                }
                line = bufferedReader.readLine();
                if (line != null && line.contains(Protocol.LOGIN + Protocol.SEPARATOR)) {
                    String[] login = line.split(Protocol.SEPARATOR);
                    if (login.length > 1 && login[0].equals(Protocol.LOGIN)) {
                        if (handleLogin(login[1])) {
                            System.out.println("New user added: " + login[1]);
                            break;
                        }
                    } else {
                        handleError();
                    }
                } else {
                    handleError();
                }
            }
            while ((line = bufferedReader.readLine()) != null) {
                if (!playing) {
                    switch (line) {
                        case Protocol.LIST:
                            handleList();
                            break;
                        case Protocol.QUEUE:
                            if (!server.getServerGames().contains(this)) {
                                server.addToQueue(userName);
                                server.createGame();
                            }
                            break;
                        case Protocol.ERROR:
                            break;
                        default:
                            handleError();
                            break;
                    }
                } else {
                    String[] message = line.split(Protocol.SEPARATOR);
                    switch (message[0]) {
                        case Protocol.MOVE:
                            if (message.length == 2) {
                                int field = Integer.parseInt(message[1]);
                                if (!serverGame.checkDisconnects()) {
                                    serverGame.makeMove(userName, field);
                                }
                            } else {
                                handleError();
                            }
                            break;
                        case Protocol.LIST:
                            handleList();
                            break;
                        case Protocol.ERROR:
                            break;
                        default:
                            handleError();
                            break;
                    }
                }
            }
        } catch (IOException e) {
            //when disconnecting
        } catch (NumberFormatException e) {
            handleError();
        } finally {
            close();
        }
    }


    /**
     * It sends an ERROR message to the client
     * and closes the connection with it, if the client
     * sent an invalid message.
     */
    public void handleError() {
        try {
            bufferedWriter.write(Protocol.ERROR);
            bufferedWriter.newLine();
            bufferedWriter.flush();
            close();
        } catch (IOException e) {
            System.err.println("An IO exception has occurred!");
        }
    }


    /**
     * Sends a LIST containing all the users that are connected to the
     * server. It is called when the client issues the LIST command.
     */
    private void handleList() {
        try {
            System.out.println(Protocol.forwardList(server.getAllNames()));
            bufferedWriter.write(Protocol.forwardList(server.getAllNames()));
            bufferedWriter.newLine();
            bufferedWriter.flush();
        } catch (IOException e) {
            System.err.println("An IO error has occurred!");
            if (hasConnection()) {
                handleError();
            }
        }
    }


    /**
     * Starts or stops the serverGame for this client, depending on, if player1
     * and player2 are empty string or not.
     *
     * @param playingLocal true is the client plays, otherwise it's false.
     * @param player1      the name of the first player
     * @param player2      the name of the second player
     * @param game         in which the client plays.
     */
    public void changeGame(Boolean playingLocal, String player1, String player2, ServerGame game) {
        this.playing = playingLocal;
        if (!player1.equals("") && !player2.equals("")) {
            try {
                serverGame = game;
                bufferedWriter.write(Protocol.sendNewGame(player1, player2));
                bufferedWriter.newLine();
                bufferedWriter.flush();
            } catch (IOException e) {
                if (hasConnection()) {
                    handleError();
                }
            }
        }

    }


    /**
     * Sends Hello back to the client according to the Protocol, if it has
     * received it from it.
     *
     * @return true if the message was sent successfully, otherwise false.
     */
    private boolean sendHello() {
        try {
            bufferedWriter.write(Protocol.sendHello(SERVER_NAME));
            bufferedWriter.newLine();
            bufferedWriter.flush();
            return true;
        } catch (IOException e) {
            System.err.println("An IO error has occurred!");
            return false;
        }
    }


    /**
     * Checks if the name provided by the client at the login
     * is unique and sends LOGIN if the server stored the name.
     * If another user with this name exists,
     * it sends ALREADYLOGGEDIN according to the Protocol.
     *
     * @param name the name that the Client provided at the login.
     * @return true if the name was unique and the client handler sent
     * LOGIN back to the client, otherwise return false if the client handler
     * sends ALREADYLOGGEDIN back.
     */
    private boolean handleLogin(String name) {
        try {
            if (server.containsName(name)) {
                bufferedWriter.write(Protocol.ALREADYLOGGEDIN);
                bufferedWriter.newLine();
                bufferedWriter.flush();
                return false;
            } else {
                server.addUser(name, this);
                this.userName = name;
                bufferedWriter.write(Protocol.LOGIN);
                bufferedWriter.newLine();
                bufferedWriter.flush();
                return true;
            }
        } catch (IOException e) {
            System.err.println("An IO error has occurred!");
            return false;
        }
    }


    /**
     * Closes the connection between the client and the client handler,
     * when the client disconnects from the server. It removes all the
     * references the client has and all the information the server stores
     * about this client is removed.
     */
    public void close() {
        try {
            if (!socket.isClosed()) {
                socket.close();
                if (server.getServerGames().contains(serverGame)) {
                    serverGame.checkDisconnects();
                }
                if (server.getQueue().contains(this.userName)) {
                    server.getQueue().remove(this.userName);
                }
                server.removeUser(this.userName, this);
                System.out.println(this.userName + " left");

                thread.join();
            }
        } catch (IOException e) {
            System.out.println("An IO error has occurred!");
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
    }
}
