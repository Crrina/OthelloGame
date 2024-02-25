package ss.othello.networking.client;


import java.net.InetAddress;

/**
 * The interface that models a Client, which connects to a Server.
 */

public interface ChatClient {


    /**
     * Connects the client to the server.
     *
     * @param address of the server.
     * @param port    of the server.
     * @return true if client got connected to the server, else false.
     */

    boolean connect(InetAddress address, int port);


    /**
     * Close the connection between the client and the server.
     */
    void close();

    /**
     * Sends the userName of the client to the server.
     *
     * @param userName to be sent.
     * @return true if the userName was sent successfully, false otherwise.
     */
    boolean sendUsername(String userName);


}

