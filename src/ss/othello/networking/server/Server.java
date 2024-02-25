package ss.othello.networking.server;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.SocketException;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;


/**
 * The class Server that implements the ChatServer and Runnable
 * interface. The Server class is responsible for starting the server,
 * accepting connections, storing the clients' information, such as
 * the usernames, creating ServerGames and stopping the server.
 */
public class Server implements ChatServer, Runnable {


    /**
     * The name of the server, that is sent with the HELLO~ message.
     */
    public static final String SERVER_NAME = "Othello server";
    private final List<String> userNames = new ArrayList<>();
    private final List<String> queue = new ArrayList<>();
    private final Map<String, ClientHandler> users = new LinkedHashMap<>();
    private final List<ServerGame> serverGames = new ArrayList<>();
    private ServerSocket serverSocket;
    private Thread thread;
    private boolean portIsFree;


    /**
     * The Server constructor, which initialises the
     * serverSocket. If the port number is not used, portIsFree
     * is set to true.
     *
     * @param port the port number used by the serverSocket.
     */
    public Server(int port) {
        try {
            serverSocket = new ServerSocket(port);
            portIsFree = true;
        } catch (IOException e) {
            portIsFree = false;
            System.out.println("The port is already in use");
        }
    }

    /**
     * Starts the Server. It creates a new thread
     * on this Server and starts it. It is called only
     * after the Server constructor is called.
     */
    @Override
    public void start() {
        thread = new Thread(this);
        thread.start();
        System.out.println("The server started at port " +
                getPort() + ". Enter 'QUIT' if you want to close it.");
    }


    /**
     * Getter for the server port number. This method is used
     * only after the server has started and has a port.
     *
     * @return the port number on which this server runs on.
     */
    @Override
    public int getPort() {
        return serverSocket.getLocalPort();
    }


    /**
     * Checks if the port is free.
     *
     * @return true if the port is free, false otherwise
     */
    public boolean isPortIsFree() {
        return this.portIsFree;
    }

    /**
     * The method that stops the server. It can be called
     * only after the server has started. It closes
     * the serverSocket, so the server can not accept more
     * connections.
     */
    @Override
    public void stop() {
        try {
            serverSocket.close();
            System.out.println("The server is down.");
            thread.join();
        } catch (IOException e) {
            // do not do anything
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
    }


    /**
     * Checks if a user is currently logged in the server, by
     * checking if its name is contained in the userNames list.
     *
     * @param userName the name of the user to be checked.
     * @return true is the userNames list contains this userName,
     * otherwise return false.
     */
    public synchronized boolean containsName(String userName) {
        return this.userNames.contains(userName);
    }


    /**
     * Gets all the ServerGames. A ServerGame is responsible
     * for handling a game between 2 clients.
     *
     * @return the list that contains all the existent
     * ServerGames.
     */
    public synchronized List<ServerGame> getServerGames() {
        return serverGames;
    }


    /**
     * Get the usernames that queued to play a game.
     *
     * @return the list that contains the usernames that queued in order
     * to play a game.
     */
    public synchronized List<String> getQueue() {
        return queue;
    }


    /**
     * When the client connects to the server, the user will be asked
     * to input a name. If the name is unique, then it will be added to
     * the userNames list and put in the users map together with its client handler.
     *
     * @param userName      the name to be added, that the user provides at log in.
     * @param clientHandler the corresponding client handler for this username.
     */
    public synchronized void addUser(String userName, ClientHandler clientHandler) {
        userNames.add(userName);
        users.put(userName, clientHandler);
    }


    /**
     * When the client disconnects from the server, this method
     * is used to remove the username from the userNames list and
     * remove its corresponding client handler from the map.
     *
     * @param userName      the name provided by the user at login.
     * @param clientHandler the client handler that handles the user with the
     *                      given name.
     */
    public synchronized void removeUser(String userName, ClientHandler clientHandler) {
        userNames.remove(userName);
        users.remove(userName, clientHandler);
    }


    /**
     * Gets the usernames of all the logged in clients. The username was
     * provided at login.
     *
     * @return the list userNames that contain all the client's username.
     */
    public synchronized List<String> getAllNames() {
        return userNames;
    }


    /**
     * Adds the name of the client to the queue game.
     * If the client issues this command a second time, then
     * the name it's removed from the queue.
     *
     * @param name of the client that is added
     *             to the queue game.
     */
    public synchronized void addToQueue(String name) {
        if (queue.contains(name)) {
            queue.remove(name);
        } else {
            queue.add(name);
        }
    }


    /**
     * This method will create a ServerGame if there are enough
     * players in the queue (size greater than or equal to 2). The player who queued first
     * will be the first to start the game. There is a call to
     * the ServerGame constructor, that is responsible for creating
     * the game. The ServerGame is added to the serverGames list.
     */
    public synchronized void createGame() {
        if (queue.size() >= 2) {
            String user1 = queue.get(0);
            String user2 = queue.get(1);
            queue.remove(user1);
            queue.remove(user2);
            // client who queues first makes the first move
            ClientHandler client1 = users.get(user1);
            ClientHandler client2 = users.get(user2);
            ServerGame serverGame = new ServerGame(client1, client2, this);

            if (!serverGame.startGame()) {
                serverGame.stopGame();
            }
            getServerGames().add(serverGame);

        }
    }


    /**
     * The run method started by the server thread.
     * While the Server Socket is not closed, it will accept
     * connections and create a new ClientHandler on a new thread
     * for each client.
     */
    @Override
    public void run() {
        while (!serverSocket.isClosed()) {
            try {
                Socket socket = serverSocket.accept();
                // call to the clientHandler,
                // when the constructor is called a clientHandler is started.
                new ClientHandler(socket, this);
            } catch (SocketException e) {
                System.err.println("Socket closed");
            } catch (IOException e) {
                System.err.println("IO exception has occurred!");
            }
        }
    }


}
